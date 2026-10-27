module

public import CFSG.LargeExtraspecial.S10EightG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem fix_τ₁_vec : ∀ (m : M2) (σ : Gm), act τ₁ m = m → m ≠ 0 → σ.1 = 1 → σ ^ 3 = 1 →
    σ ≠ 1 → m = E00 ∨ m = act σ E00 ∨ m = act (σ * σ) E00 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem isPGroup_Lbar_subgroupOf (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    IsPGroup 2 ((S.Lbar g).subgroupOf S.Mbar) := by
  intro x
  refine ⟨1, ?_⟩
  have h1 : ((x : S.Mbar) : S.O) * ((x : S.Mbar) : S.O) = 1 :=
    S4.mul_self_of_mem_Lbar S haQ (mem_subgroupOf.mp x.2)
  have h2 : (x : S.Mbar) * (x : S.Mbar) = 1 := Subtype.ext h1
  have h3 : x * x = 1 := Subtype.ext h2
  rw [pow_one, _root_.sq, h3]

theorem comm_Lbar_subgroupOf (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∀ a ∈ (S.Lbar g).subgroupOf S.Mbar, ∀ b ∈ (S.Lbar g).subgroupOf S.Mbar, a * b = b * a :=
  fun _ ha _ hb => Subtype.ext (S4.Lbar_comm S haQ (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb))

theorem mem_map_subgroupOf_iff {h : S.M} {x : S.Mbar} (hh : S.ρ h = (x : S.O)) (y : S.Mbar) :
    y ∈ ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ↔
      (y : S.O) ∈ S.Lbar ((h : G) * g) := by
  rw [mem_map_conj_iff, mem_subgroupOf, mem_Lbar_mul_iff, hh]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem isWeaklyClosed_Lbar_subgroupOf (C : Cons311 S g) :
    IsWeaklyClosedInNormalizer ((S.Lbar g).subgroupOf S.Mbar) := by
  intro x hx
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  obtain ⟨h, hh⟩ : ∃ h : S.M, S.ρ h = (x : S.O) := MonoidHom.mem_range.mp x.2
  have hle : S.Lbar ((h : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro y hy
    have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar _ hy
    have hyN := hx ((mem_map_subgroupOf_iff hh ⟨y, hyM⟩).mpr hy)
    rw [mem_normalizer_iff] at hyN ⊢
    intro w
    constructor
    · intro hw'
      exact mem_subgroupOf.mp ((hyN ⟨w, hLM hw'⟩).mp (mem_subgroupOf.mpr hw'))
    · intro hw'
      have hwM : w ∈ S.Mbar := by
        have h1 : w = y⁻¹ * (y * w * y⁻¹) * y := by group
        rw [h1]
        exact mul_mem (mul_mem (inv_mem hyM) (hLM hw')) hyM
      exact mem_subgroupOf.mp ((hyN ⟨w, hwM⟩).mpr (mem_subgroupOf.mpr hw'))
  have heq := C.weaklyClosed (h : G) h.2 hle
  ext y
  rw [mem_map_subgroupOf_iff hh, heq, mem_subgroupOf]

theorem Hyp10.conj_mem_Lbar_of_commute (X : Hyp10 S g t) {l m : S.O} (hl : l ∈ S.Lbar g)
    (hm : m ∈ S.Mbar) (hc : ∀ x ∈ S.Lbar g, m * l * m⁻¹ * x = x * (m * l * m⁻¹)) :
    m * l * m⁻¹ ∈ S.Lbar g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  have hsc := lemma_3_12_isStronglyClosedIn (isPGroup_Lbar_subgroupOf X.haQ)
    (comm_Lbar_subgroupOf X.haQ) (isWeaklyClosed_Lbar_subgroupOf X.C)
  have hl' : (⟨l, hLM hl⟩ : S.Mbar) ∈ (S.Lbar g).subgroupOf S.Mbar := mem_subgroupOf.mpr hl
  have key := hsc.2 ⟨l, hLM hl⟩ hl' (⟨m, hm⟩ : S.Mbar)⁻¹ (by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : ((x : S.Mbar) : S.O) ∈ S.Lbar g := mem_subgroupOf.mp hx
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact (hc _ hx').symm)
  have := mem_subgroupOf.mp key
  simpa using this

theorem inv_commute_of_commute {k : S.M} (hk : S.ρ k * t = t * S.ρ k) :
    S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
  rw [map_inv]
  calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
    _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hk]
    _ = t * (S.ρ k)⁻¹ := by group

theorem mem_line_of_fix {τ : S.O} (Y : Hyp10 S g τ) (F : Frame Y) {x₀ : S.O}
    (hx₀R : x₀ ∈ Rbar S g τ) (hπx₀ : F.π ⟨x₀, hx₀R⟩ = τ₁) {d : S.O} (hdR : d ∈ Rbar S g τ)
    (hσ1 : (F.π ⟨d, hdR⟩).1 = 1) (hσ3 : F.π ⟨d, hdR⟩ ^ 3 = 1) (hσne : F.π ⟨d, hdR⟩ ≠ 1)
    {w : Vt S g τ} (hw0 : w ≠ 0) (hfix : resV Y.haQ τ ⟨x₀, hx₀R⟩ w = w) :
    w = aV Y.ht ∨ w = resV Y.haQ τ ⟨d, hdR⟩ (aV Y.ht) ∨
      w = resV Y.haQ τ ⟨d * d, mul_mem hdR hdR⟩ (aV Y.ht) := by
  have h1 := congrArg F.φ hfix
  rw [F.compat, hπx₀] at h1
  have hφ0 : F.φ w ≠ 0 := fun h => hw0 (F.φ.injective (h.trans (map_zero _).symm))
  rcases fix_τ₁_vec _ _ h1 hφ0 hσ1 hσ3 hσne with h | h | h
  · exact Or.inl (F.φ.injective (by rw [h, F.base]))
  · exact Or.inr (Or.inl (F.φ.injective (by rw [h, F.φ_resV_aV])))
  · refine Or.inr (Or.inr (F.φ.injective ?_))
    rw [h, F.φ_resV_aV, ← map_mul]
    rfl

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem conj_mem_Xb (hCE : CentralExtInput.{u}) {k : S.M} (hk : S.ρ k * t = t * S.ρ k)
    (hkE : ∀ e ∈ S.Lbar g ⊓ Xb, S.ρ k * e = e * S.ρ k) {x : S.O} (hx : x ∈ Xb) :
    S.ρ k * x * (S.ρ k)⁻¹ ∈ Xb := by
  obtain ⟨F, -, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨x₀, hx₀L, hπx₀⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inl rfl))
  have hx₀X : x₀ ∈ Xb := by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨_, by rw [hπx₀]; exact τ₁_mem_Γ₁⟩
  have hNX := D.dec.Nbar_le hCE X
  have hle : F.pre Γ₁ ≤ Xb.comap (MulAut.conj (S.ρ k)).toMonoidHom := by
    refine F.pre_Γ₁_le_of hx₀L hπx₀ (fun n hn => ?_) (fun r hr => ?_)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hNX (conj_mem_Nbar X.haQ hk hn)
    · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hrk := conj_mem_Rbar hk hr
      have e1 : S.ρ k * (r * x₀ * r⁻¹) * (S.ρ k)⁻¹ =
          (S.ρ k * r * (S.ρ k)⁻¹) * x₀ * (S.ρ k * r * (S.ρ k)⁻¹)⁻¹ := by
        have hx₀k : S.ρ k * x₀ * (S.ρ k)⁻¹ = x₀ := by
          rw [hkE x₀ ⟨hx₀L, hx₀X⟩]
          group
        calc S.ρ k * (r * x₀ * r⁻¹) * (S.ρ k)⁻¹ =
              (S.ρ k * r * (S.ρ k)⁻¹) * (S.ρ k * x₀ * (S.ρ k)⁻¹) *
                (S.ρ k * r * (S.ρ k)⁻¹)⁻¹ := by group
          _ = _ := by rw [hx₀k]
      rw [e1, hFX]
      exact F.conj_mem_pre_Γ₁ hrk (hFX ▸ hx₀X)
  rw [hFX] at hx
  have := hle hx
  simpa using this

theorem exists_Lbar_eq_of_commute (hCE : CentralExtInput.{u}) {d : S.O} (hd : d ∈ ⁅Yb, Yb⁆)
    (hd1 : d ≠ 1) {k : S.M} (hk : S.ρ k * t = t * S.ρ k)
    (hkE : ∀ e ∈ S.Lbar g ⊓ Xb, S.ρ k * e = e * S.ρ k) :
    ∃ k₁ : S.M, (S.ρ k₁ = 1 ∨ S.ρ k₁ = d ∨ S.ρ k₁ = d * d) ∧
      S.Lbar ((k : G) * g) = S.Lbar ((k₁ : G) * g) := by
  obtain ⟨F, hFY, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨hσ1, hσ3, hσne⟩ := D.dec.pi_spec hCE hFY hd hd1
  obtain ⟨x₀, hx₀L, hπx₀⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inl rfl))
  have hx₀X : x₀ ∈ Xb := by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨_, by rw [hπx₀]; exact τ₁_mem_Γ₁⟩
  have hth : t ∈ S.Lbar ((k : G) * g) := by
    have h := conj_mem_Lbar_mul S k X.ht
    rwa [show S.ρ k * t * (S.ρ k)⁻¹ = t by rw [hk]; group] at h
  have hfix : resV X.haQ t ⟨x₀, Lbar_le_Rbar X.ht hx₀L⟩ (bV hth) = bV hth := by
    refine Subtype.ext ?_
    rw [coe_resV_apply, coe_bV, ← ρ_cl_conj_z S k X.haQ]
    have hx₀k : x₀ * S.ρ k = S.ρ k * x₀ := (hkE x₀ ⟨hx₀L, hx₀X⟩).symm
    have h1 : ((x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
      S.mem_fixLbar.mp (S.cl_mem_fixLbar_self X.haQ) x₀ hx₀L
    calc ((x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl (g * S.z * g⁻¹))) =
          ((x₀ * S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := rfl
      _ = ((S.ρ k * x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by rw [hx₀k]
      _ = ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
          change ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((x₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = _
          rw [h1]
  have hdR := D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).mp hd).1
  obtain ⟨kd, hkd⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hdR)
  rcases mem_line_of_fix X F (Lbar_le_Rbar X.ht hx₀L) hπx₀ hdR hσ1 hσ3 hσne
    (bV_ne_zero X.H hth) hfix with h | h | h
  · refine ⟨1, Or.inl (map_one _), ?_⟩
    have h1 := congrArg Subtype.val h
    rw [coe_bV] at h1
    rw [Subgroup.coe_one, one_mul]
    exact Lbar_eq_of_cl_eq S X.haQ X.H.conj_ne (conj_mem_QG' S k.2 X.haQ) h1
  · refine ⟨kd, Or.inr (Or.inl hkd), ?_⟩
    have h1 := congrArg Subtype.val h
    rw [coe_bV, coe_resV_apply] at h1
    have h2 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
        ((d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := h1
    rw [← hkd, ρ_cl_conj_z S kd X.haQ] at h2
    exact Lbar_eq_of_cl_eq S (conj_mem_QG' S kd.2 X.haQ) (conj_ne_z' S kd.2 X.H.conj_ne)
      (conj_mem_QG' S k.2 X.haQ) h2
  · refine ⟨kd * kd, Or.inr (Or.inr (by rw [map_mul, hkd])), ?_⟩
    have h1 := congrArg Subtype.val h
    rw [coe_bV, coe_resV_apply] at h1
    have h2 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
        ((d * d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := h1
    rw [show d * d = S.ρ (kd * kd) by rw [map_mul, hkd], ρ_cl_conj_z S (kd * kd) X.haQ] at h2
    exact Lbar_eq_of_cl_eq S (conj_mem_QG' S (kd * kd).2 X.haQ)
      (conj_ne_z' S (kd * kd).2 X.H.conj_ne) (conj_mem_QG' S k.2 X.haQ) h2

end Dec108

end CFSG.LargeExtraspecial.S10
