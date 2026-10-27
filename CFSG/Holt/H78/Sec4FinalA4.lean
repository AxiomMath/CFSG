module

public import CFSG.Holt.H78.Sec4FinalA3

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section Embed

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [FaithfulSMul G Ω] in
theorem eq_of_psi_eq_of_isPGroup (hS : Sec4Setting G Ω) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXst : X ≤ stabilizer G α ⊓ stabilizer G β)
    (hXB : ∀ g ∈ X, ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g • δ = δ)
    {g₁ g₂ : G} (h₁ : g₁ ∈ X) (h₂ : g₂ ∈ X)
    (h : C.psi ⟨g₁, stabilizer_inf_le_stabilizer_pair α β (hXst h₁)⟩ =
      C.psi ⟨g₂, stabilizer_inf_le_stabilizer_pair α β (hXst h₂)⟩) : g₁ = g₂ := by
  have h₁₂ : g₁ * g₂⁻¹ ∈ X := mul_mem h₁ (inv_mem h₂)
  obtain ⟨k, hk⟩ := hX ⟨_, h₁₂⟩
  have hk' : (g₁ * g₂⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hp₁ := stabilizer_inf_le_stabilizer_pair α β (hXst h₁)
  have hp₂ := stabilizer_inf_le_stabilizer_pair α β (hXst h₂)
  refine mul_inv_eq_one.mp (C.eq_one_of_psi_eq_one hS hk' (hXst h₁₂) ?_ (hXB _ h₁₂))
  rw [C.psi_mul hp₁ (inv_mem hp₂), C.psi_inv hp₂, h, mul_inv_cancel]

omit [FaithfulSMul G Ω] in
theorem commute_of_psi_eq_one (hS : Sec4Setting G Ω) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXst : X ≤ stabilizer G α ⊓ stabilizer G β)
    (hXB : ∀ g ∈ X, ∀ δ ∈ holtDelta G Ω α β, δ ∈ fixSet Ω (Subgroup.zpowers v) → g • δ = δ)
    {k : G} (hk : k ∈ stabilizer G ({α, β} : Set Ω)) (hψk : C.psi ⟨k, hk⟩ = 1)
    (hkX : ∀ g ∈ X, k * g * k⁻¹ ∈ X) {g : G} (hg : g ∈ X) : k * g = g * k := by
  have hgp := stabilizer_inf_le_stabilizer_pair α β (hXst hg)
  have h := C.eq_of_psi_eq_of_isPGroup hS hX hXst hXB (hkX g hg) hg (by
    rw [C.psi_mul (mul_mem hk hgp) (inv_mem hk), C.psi_mul hk hgp, C.psi_inv hk, hψk, one_mul,
      inv_one, mul_one])
  exact mul_inv_eq_iff_eq_mul.mp h

theorem commute_x_of_le_fixingSubgroup (hS : Sec4Setting G Ω) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXF : X ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hxX : ∀ g ∈ X, C.x * g * C.x⁻¹ ∈ X) {g : G} (hg : g ∈ X) : C.x * g = g * C.x := by
  have hfix : ∀ g ∈ X, ∀ ω ∈ fixSet Ω (Subgroup.zpowers v), g • ω = ω := fun g hg =>
    (mem_fixingSubgroup_iff G).mp (hXF hg)
  refine C.commute_of_psi_eq_one hS hX (fun g hg => Subgroup.mem_inf.mpr
    ⟨mem_stabilizer_iff.mpr (hfix g hg α C.isTypeL.mem_fixSet),
      mem_stabilizer_iff.mpr (hfix g hg β C.mem_fixSet)⟩) (fun g hg δ _ hδ => hfix g hg δ hδ)
    (C.x_mem_stabilizer_pair hS) (C.psi_x hS) hxX hg

end Embed

section LiftX

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_twoPointKernel_of_mem_pair {g k : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hk : k ∈ twoPointKernel G Ω α β) : g * k * g⁻¹ ∈ twoPointKernel G Ω α β := by
  obtain ⟨hkα, hkβ, hkΔ⟩ := mem_twoPointKernel.mp hk
  have hgΔ := stabilizer_pair_le α β hg
  have hg' : g⁻¹ ∈ stabilizer G ({α, β} : Set Ω) := inv_mem hg
  have hfix : ∀ ω ∈ ({α, β} : Set Ω), (g * k * g⁻¹) • ω = ω := fun ω hω => by
    have h1 : g⁻¹ • ω ∈ ({α, β} : Set Ω) := by
      rw [← mem_stabilizer_iff.mp hg']
      exact Set.smul_mem_smul_set hω
    have h2 : k • g⁻¹ • ω = g⁻¹ • ω := by
      rcases h1 with h1 | h1
      · rw [h1, hkα]
      · rw [Set.mem_singleton_iff.mp h1, hkβ]
    rw [mul_smul, mul_smul, h2, smul_inv_smul]
  refine mem_twoPointKernel.mpr ⟨hfix α (Set.mem_insert α _), hfix β (by simp), fun δ hδ => ?_⟩
  have h1 : g⁻¹ • δ ∈ holtDelta G Ω α β := by
    rw [← mem_stabilizer_iff.mp (inv_mem hgΔ)]
    exact Set.smul_mem_smul_set hδ
  rw [mul_smul, mul_smul, hkΔ _ h1, smul_inv_smul]

theorem exists_centralizer_x (hS : Sec4Setting G Ω) {n : Equiv.Perm C.Psi} (hn : n ∈ C.N) :
    ∃ g, ∃ hg : g ∈ stabilizer G α ⊓ stabilizer G β, g * C.x = C.x * g ∧
      C.psi ⟨g, stabilizer_inf_le_stabilizer_pair α β hg⟩ = n := by
  obtain ⟨l, hlL, rfl⟩ := C.D.mem_M.mp hn
  have hxJ := C.x_mem_closure hS
  have hxp := C.x_mem_stabilizer_pair hS
  set xh : twoPointSection G Ω α β := twoPointElt hxp with hxh
  have hxhH : xh ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    twoPointElt_mem_jHull hS.star hxJ
  have hxhS : xh ∉ C.D.socPre := fun h =>
    C.ne (((C.smul_eq_iff_mem_socPre hS hxJ).mpr h).symm.trans (C.x_smul hS).1)
  have hρx : C.D.ρ C.i₀ ⟨xh, hxhH⟩ = 1 := by
    rw [← C.psi_x hS]
    exact (C.psi_eq_rho hS hxJ).symm
  have hlH := l.2
  have hcxH : (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ ∈
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    mul_mem (mul_mem hlH hxhH) (inv_mem hlH)
  have hcxS : (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ ∉
      C.D.socPre := fun h => hxhS (by
    have h1 := C.D.conj_mem_socPre (inv_mem hlH) h
    rwa [show (l : twoPointSection G Ω α β)⁻¹ * ((l : twoPointSection G Ω α β) * xh *
      (l : twoPointSection G Ω α β)⁻¹) * (l : twoPointSection G Ω α β)⁻¹⁻¹ = xh by group] at h1)
  have hoO : (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ * xh⁻¹ ∈
      jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    have hk := (C.D.mem_jOrbitKernel_iff_rho
      (h := l * ⟨xh, hxhH⟩ * l⁻¹ * (⟨xh, hxhH⟩ : jHull _ _)⁻¹)).mpr fun j => by
        rcases C.eq_i₀ j with rfl
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρx]
        group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk
    rw [← C.D.socPre_inf_jOrbitKernel]
    exact Subgroup.mem_inf.mpr ⟨(C.mul_mem_socPre_iff hS hcxH (inv_mem hxhH)).mpr
      (iff_of_false hcxS fun h => hxhS (by simpa using inv_mem h)), hk⟩
  set o := (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ * xh⁻¹ with ho
  have hxh2 : xh * xh = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hxh, ← map_mul]
    exact (congrArg (twoPointHom G Ω α β) (Subtype.ext (C.x_mul_self hS) :
      (⟨C.x, hxp⟩ : stabilizer G ({α, β} : Set Ω)) * ⟨C.x, hxp⟩ = 1)).trans (map_one _))
  have hox : o * xh = (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ := by
    rw [ho, inv_mul_cancel_right]
  have hu2 : o * xh * (o * xh) = 1 := by
    rw [hox, show (l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹ *
      ((l : twoPointSection G Ω α β) * xh * (l : twoPointSection G Ω α β)⁻¹) =
        (l : twoPointSection G Ω α β) * (xh * xh) * (l : twoPointSection G Ω α β)⁻¹ by group,
      hxh2, mul_one, mul_inv_cancel]
  have hxox : xh * (o * xh) ∈ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    have h1 := (jOddCore_normal (G := twoPointSection G Ω α β)
      (Ω := holtDelta G Ω α β)).conj_mem o hoO xh
    rwa [show xh * o * xh⁻¹ = xh * (o * xh) by
      rw [inv_eq_of_mul_eq_one_right hxh2, mul_assoc]] at h1
  obtain ⟨y, hy, hyx⟩ := exists_mem_zpowers_conj_eq_of_odd hxh2 hu2
    (odd_card_jOddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxox))
  have hyO : y ∈ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    Subgroup.zpowers_le.mpr hxox hy
  have hyH : y ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) := jOddCore_le_jHull hyO
  set c' := y⁻¹ * (l : twoPointSection G Ω α β) with hc'
  have hc'x : c' * xh = xh * c' := by
    have h1 : c' * xh * c'⁻¹ = xh := by
      rw [hc', show y⁻¹ * (l : twoPointSection G Ω α β) * xh * (y⁻¹ *
        (l : twoPointSection G Ω α β))⁻¹ = y⁻¹ * ((l : twoPointSection G Ω α β) * xh *
          (l : twoPointSection G Ω α β)⁻¹) * y by group, ← hox, ← hyx]
      group
    calc c' * xh = c' * xh * c'⁻¹ * c' := by group
      _ = xh * c' := by rw [h1]
  have hc'L : c' ∈ C.D.L C.i₀ := mul_mem (inv_mem (C.D.oddCore_le C.i₀ hyO)) hlL
  have hc'H : c' ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    mul_mem (inv_mem hyH) hlH
  have hρc' : C.D.ρ C.i₀ ⟨c', hc'H⟩ = C.D.ρ C.i₀ l := by
    rw [show (⟨c', hc'H⟩ : jHull _ _) = (⟨y, hyH⟩ : jHull _ _)⁻¹ * l from rfl, map_mul, map_inv,
      C.D.rho_eq_one_of_mem_jOddCore (h := ⟨y, hyH⟩) hyO, inv_one, one_mul]
  have hc'J : ((c' : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) ∈
      twoPointJ G Ω α β := by
    rw [hS.twoPointJ_eq_map_jHull]
    exact ⟨c', hc'H, rfl⟩
  obtain ⟨c, hcJ, hcc'⟩ := mem_twoPointJ.mp hc'J
  have hcp := closure_longInvSwap_le_stabilizer_pair α β hcJ
  have hcĉ : twoPointElt hcp = c' := Subtype.ext (Equiv.ext fun δ => Subtype.ext (hcc' δ).symm)
  have hcα : c • α = α := by
    rw [C.smul_eq_iff_mem_socPre hS hcJ, hcĉ]
    exact C.D.L_le_socPre C.i₀ hc'L
  have hcβ : c • β = β := by
    rcases smul_pair_of_mem_stabilizer_pair hcp with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (hcα.symm.trans h) C.ne
  obtain ⟨hxα, hxβ, -⟩ := C.x_smul hS
  have hcomΔ : ∀ δ ∈ holtDelta G Ω α β, c • C.x • δ = C.x • c • δ := fun δ hδ => by
    have h1 := congrArg (fun π : twoPointSection G Ω α β =>
      (((π : Equiv.Perm (holtDelta G Ω α β)) ⟨δ, hδ⟩ : holtDelta G Ω α β) : Ω)) hc'x
    rw [← hcĉ] at h1
    exact h1
  set k₀ := c * C.x * c⁻¹ * C.x⁻¹ with hk₀
  have hk₀K : k₀ ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel.mpr ⟨?_, ?_, fun δ hδ => ?_⟩
    · rw [hk₀, mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.mpr hxβ.symm,
        inv_smul_eq_iff.mpr hcβ.symm, hxβ, hcα]
    · rw [hk₀, mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.mpr hxα.symm,
        inv_smul_eq_iff.mpr hcα.symm, hxα, hcβ]
    · have hδ' : c⁻¹ • C.x⁻¹ • δ ∈ holtDelta G Ω α β :=
        smul_mem_holtDelta_of_mem_inf (inv_mem (Subgroup.mem_inf.mpr ⟨hcα, hcβ⟩))
          (by
            have h1 := stabilizer_pair_le α β (inv_mem hxp)
            rw [← mem_stabilizer_iff.mp h1]
            exact Set.smul_mem_smul_set hδ)
      rw [hk₀, mul_smul, mul_smul, mul_smul, hcomΔ _ hδ', smul_inv_smul, smul_inv_smul]
  have hx2 := C.x_mul_self hS
  have hck : c * C.x * c⁻¹ = k₀ * C.x := by rw [hk₀, inv_mul_cancel_right]
  have hkx2 : k₀ * C.x * (k₀ * C.x) = 1 := by
    rw [← hck, show c * C.x * c⁻¹ * (c * C.x * c⁻¹) = c * (C.x * C.x) * c⁻¹ by group, hx2,
      mul_one, mul_inv_cancel]
  have hxkx : C.x * (k₀ * C.x) ∈ twoPointKernel G Ω α β := by
    have h1 := conj_mem_twoPointKernel_of_mem_pair hxp hk₀K
    rwa [inv_eq_of_mul_eq_one_right hx2, mul_assoc] at h1
  obtain ⟨y', hy', hy'x⟩ := exists_mem_zpowers_conj_eq_of_odd hx2 hkx2
    (C.odd_twoPointKernel.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxkx))
  have hy'K : y' ∈ twoPointKernel G Ω α β := Subgroup.zpowers_le.mpr hxkx hy'
  have hy'st := twoPointKernel_le_inf hy'K
  have hy'p := stabilizer_inf_le_stabilizer_pair α β hy'st
  have hcst : c ∈ stabilizer G α ⊓ stabilizer G β := Subgroup.mem_inf.mpr ⟨hcα, hcβ⟩
  refine ⟨y'⁻¹ * c, mul_mem (inv_mem hy'st) hcst, ?_, ?_⟩
  · have h1 : y'⁻¹ * c * C.x * (y'⁻¹ * c)⁻¹ = C.x := by
      rw [show y'⁻¹ * c * C.x * (y'⁻¹ * c)⁻¹ = y'⁻¹ * (c * C.x * c⁻¹) * y' by group, hck,
        ← hy'x]
      group
    calc y'⁻¹ * c * C.x = y'⁻¹ * c * C.x * (y'⁻¹ * c)⁻¹ * (y'⁻¹ * c) := by group
      _ = C.x * (y'⁻¹ * c) := by rw [h1]
  · have hψy' : C.psi ⟨y', hy'p⟩ = 1 := (C.psi_eq_one_iff _).mpr fun δ => by
      have h1 : twoPointHom G Ω α β ⟨y', hy'p⟩ δ = δ :=
        Subtype.ext ((mem_twoPointKernel.mp hy'K).2.2 δ δ.2)
      rw [h1]
      exact mem_orbit_self δ
    rw [C.psi_mul (inv_mem hy'p) hcp, C.psi_inv hy'p, hψy', inv_one, one_mul,
      C.psi_eq_rho hS hcJ, ← hρc']
    exact congrArg _ (Subtype.ext hcĉ)

theorem eq_γ_of_x_smul_eq (hS : Sec4Setting G Ω) {δ : holtDelta G Ω α β}
    (hδΦ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) (hxδ : C.x • (δ : Ω) = δ) : δ = C.γ := by
  have hxv := C.mul_mem_longInvAt hS (C.v_mem_Z hS) C.v_ne_one
  obtain ⟨ω₀, -, huniq⟩ := hxv.1.2
  have h1 : (C.x * v) • (δ : Ω) = δ := by
    rw [mul_smul, v_smul_eq (⟨(δ : Ω), hδΦ⟩ : fixSet Ω (Subgroup.zpowers v)), hxδ]
  exact Subtype.ext ((huniq _ h1).trans (huniq _ hxv.2).symm)

theorem existsUnique_fixed_x (hS : Sec4Setting G Ω) (c : C.Psi) :
    ∃! δ : holtDelta G Ω α β, C.D.coord δ C.i₀ = c ∧ C.x • (δ : Ω) = δ := by
  have := (C.D.factor C.i₀).isPretransitive
  obtain ⟨n, hn⟩ := exists_smul_eq (C.D.M C.i₀) C.bγ c
  obtain ⟨g, hg, hgx, hψg⟩ := C.exists_centralizer_x hS n.2
  have hgp := stabilizer_inf_le_stabilizer_pair α β hg
  have hcoord : ∀ δ : holtDelta G Ω α β, C.D.coord ⟨g • (δ : Ω),
      smul_mem_holtDelta_of_mem_inf hg δ.2⟩ C.i₀ = C.psi ⟨g, hgp⟩ (C.D.coord δ C.i₀) := fun δ =>
    (C.psi_coord ⟨g, hgp⟩ δ).symm
  refine ⟨⟨g • (C.γ : Ω), smul_mem_holtDelta_of_mem_inf hg C.γ.2⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hcoord, hψg]
    exact hn
  · change C.x • g • (C.γ : Ω) = g • (C.γ : Ω)
    rw [← mul_smul, ← hgx, mul_smul, (C.x_smul hS).2.2]
  · rintro δ' ⟨hδ'c, hxδ'⟩
    have hgi : g⁻¹ ∈ stabilizer G α ⊓ stabilizer G β := inv_mem hg
    set ε : holtDelta G Ω α β := ⟨g⁻¹ • (δ' : Ω), smul_mem_holtDelta_of_mem_inf hgi δ'.2⟩
    have hεc : C.D.coord ε C.i₀ = C.bγ := by
      have h1 := C.psi_coord ⟨g⁻¹, stabilizer_inf_le_stabilizer_pair α β hgi⟩ δ'
      rw [hδ'c, C.psi_inv hgp, hψg, ← hn] at h1
      change C.D.coord (twoPointHom G Ω α β ⟨g⁻¹, stabilizer_inf_le_stabilizer_pair α β hgi⟩ δ')
        C.i₀ = C.bγ
      rw [← h1]
      change ((n : Equiv.Perm C.Psi))⁻¹ ((n : Equiv.Perm C.Psi) C.bγ) = C.bγ
      exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
    have hxε : C.x • (ε : Ω) = ε := by
      change C.x • g⁻¹ • (δ' : Ω) = g⁻¹ • (δ' : Ω)
      have hgx' : g⁻¹ * C.x = C.x * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgx, mul_assoc, mul_inv_cancel, mul_one]
      rw [← mul_smul, ← hgx', mul_smul, hxδ']
    have hεγ := C.eq_γ_of_x_smul_eq hS ((C.coord_eq_bγ_iff ε).mp hεc) hxε
    refine Subtype.ext ?_
    change (δ' : Ω) = g • (C.γ : Ω)
    rw [← hεγ]
    change (δ' : Ω) = g • g⁻¹ • (δ' : Ω)
    rw [smul_inv_smul]

end LiftX

section TorusM

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem centralizer_Y_le (hS : Sec4Setting G Ω) :
    Subgroup.centralizer (C.Y : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  Subgroup.centralizer_le (Subgroup.zpowers_le.mpr (C.Z_le_Y (C.v_mem_Z hS)))

theorem exists_centralizer_Y_of_mem_jHull (hS : Sec4Setting G Ω) {l : typeLSection G Ω v}
    (hl : l ∈ jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :
    ∃ h ∈ Subgroup.centralizer (C.Y : Set G), ∀ ω : fixSet Ω (Subgroup.zpowers v),
      (((l : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω : fixSet Ω _) : Ω) = h • (ω : Ω) := by
  have hV := C.isPGroup_zpowers
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hY2 : IsPGroup 2 C.Y := C.sylow.2.1.to_le C.Y_le_S
  induction hl using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨c, hcJ, hcC, hcu⟩ := (hS.mem_longInv_centralizerImage_iff hV h3 u).mp hu
    obtain ⟨c', -, hc'Y, hc'c⟩ := hS.frattini h3 hY2 (C.Y_le_fixingSubgroup hS) hcJ
      (centralizer_le_stabilizer_fixSet _ hcC)
    exact ⟨c', hc'Y, fun ω => (hcu ω).trans (hc'c ω ω.2).symm⟩
  | one => exact ⟨1, one_mem _, fun ω => (one_smul G (ω : Ω)).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨hx, hxY, hxe⟩ := ihx
    obtain ⟨hy, hyY, hye⟩ := ihy
    refine ⟨hx * hy, mul_mem hxY hyY, fun ω => ?_⟩
    change (((x : Equiv.Perm _) ((y : Equiv.Perm _) ω) : fixSet Ω _) : Ω) = _
    rw [hxe, hye, mul_smul]
  | inv x _ ih =>
    obtain ⟨hx, hxY, hxe⟩ := ih
    refine ⟨hx⁻¹, inv_mem hxY, fun ω => ?_⟩
    rw [eq_inv_smul_iff, ← hxe]
    change ((((x * x⁻¹ : typeLSection G Ω v) : Equiv.Perm _) ω : fixSet Ω _) : Ω) = ω
    rw [mul_inv_cancel]
    rfl

end TorusM

section Facts

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Z_of_mem_Y_of_mul_self {y : G} (hy : y ∈ C.Y) (hy2 : y * y = 1) : y ∈ C.Z := by
  have hyp := C.X_le_stabilizer_pair (C.Y_le_X hy)
  have hR := C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy)
  refine C.mem_Z.mpr ⟨hy, C.isNaturalSE_N.mem_rootCenter_seRadical (seRadical_le hR)
    (apply_eq_of_mem_seRadical hR) ?_⟩
  rw [← C.psi_mul hyp hyp, show (⟨y * y, mul_mem hyp hyp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
    from Subtype.ext hy2, map_one]

theorem smul_eq_iff_piM_apply_eq (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (ω : fixSet Ω (Subgroup.zpowers v)) :
    (g : G) • (ω : Ω) = ω ↔ C.piM hS g (C.Dv.coord ω C.i) = C.Dv.coord ω C.i := by
  rw [C.piM_coord]
  constructor
  · intro h
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext h)
  · intro h
    have h1 := congrArg Subtype.val (C.coord_Dv_injective
      (show C.Dv.coord (centralizerImageElt (Ω := Ω) g.2 • ω) = C.Dv.coord ω from
        funext fun j => by rcases C.eq_i hS j with rfl; exact h))
    exact h1

theorem piM_eq_rho (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hgH : centralizerImageElt (Ω := Ω) g.2 ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :
    C.piM hS g = C.Dv.ρ C.i ⟨_, hgH⟩ := by
  ext c
  obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
  rw [C.piM_coord, ← C.Dv.coord_smul]

theorem piM_x (hS : Sec4Setting G Ω) :
    C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ ∈ C.Dv.M C.i ∧
      orderOf (C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩) = 2 ∧
        C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ (C.Dv.coord C.a C.i) = C.Dv.coord C.b C.i ∧
          C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩
            (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i := by
  have hρ := C.Dv.rho_mem_longInv (C.x_phi_mem_longInv hS) C.i
  have he : C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ = C.Dv.ρ C.i (C.xH hS) :=
    C.piM_eq_rho hS _ (C.xH hS).2
  rw [he]
  refine ⟨C.Dv.rho_mem_M_of_isNaturalSE (C.isNaturalSE_Dv C.i) _, hρ.1, ?_, ?_⟩
  · rw [← C.Dv.coord_smul]
    exact congrArg (fun p => C.Dv.coord p C.i) (C.x_phi_smul_a hS)
  · rw [← C.Dv.coord_smul]
    exact congrArg (fun p => C.Dv.coord p C.i) (Subtype.ext (C.x_smul hS).2.2)

end Facts

end FinConfig

end CFSG.Holt.H78
