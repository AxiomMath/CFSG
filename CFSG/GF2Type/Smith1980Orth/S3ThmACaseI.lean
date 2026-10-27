module

public import CFSG.GF2Type.Smith1980Orth.S3Bad
public import CFSG.GF2Type.Smith1980Orth.S3CaseB
public import CFSG.GF2Type.Smith1980Orth.S3Count
public import CFSG.GF2Type.Smith1980Orth.S3ThmALin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem q_eq_zero_of_mem_commQt_of_mem_clSub {x : G} (hxM : x ∈ S.M) (hx2 : x ^ 2 = 1)
    {v : S.Qt} (hv : v ∈ S.commQt x)
    (hv' : v ∈ S.clSub (S.QG ⊓ centralizer ({x} : Set G))) : S.q v = 0 := by
  obtain ⟨y, hy, rfl⟩ := (S.mem_commQt_iff hxM).mp hv
  have hxx : x * x = 1 := by rw [← pow_two, hx2]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hgQ : x * y * x⁻¹ * y⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG hxM hy) (S.QG.inv_mem hy)
  obtain ⟨u, hu, huQ, hcl⟩ := S.mem_clSub_iff.mp hv'
  have hux : u * x = x * u := mem_centralizer_singleton_iff.mp hu.2
  have hgx : x * y * x⁻¹ * y⁻¹ * x = x * (x * y * x⁻¹ * y⁻¹) := by
    rcases (S.cl_eq_cl_iff huQ hgQ).mp hcl with e | e
    · rw [e]
      exact hux
    · rw [e, mul_assoc, ← S.z_comm hxM, ← mul_assoc, hux, mul_assoc]
  rw [S.q_cl_eq_zero_iff hgQ]
  have hinv : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h1 : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) =
        (x * x) * y * (x * x)⁻¹ * y⁻¹ := by group
    rw [h1, hxx]
    group
  have hfix : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    rw [← hgx]
    group
  rw [hfix] at hinv
  rw [pow_two]
  calc (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) =
      (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ := by rw [← hinv]
    _ = 1 := mul_inv_cancel _

namespace S2Data

section Rel

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

theorem card_le_two_mul_card_inf_Cbar_of_isPGroup {H : Subgroup S.O} (hH : H ≤ M1)
    (h2 : IsPGroup 2 H) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ D.Cbar : Subgroup S.O) := by
  classical
  let P : Subgroup S.O := D.Obar ⊔ zpowers D.t
  have hdec0 : ∀ h : H, ∃ s : ↥P, ∃ c : D.Cbar, (h : S.O) = (s : S.O) * (c : S.O) := by
    intro h
    obtain ⟨s, hs, c, hc, e⟩ := D.exists_mul_Cbar_of_mem_M1 (hH h.2)
    exact ⟨⟨s, hs⟩, ⟨c, hc⟩, e⟩
  let sf : H → ↥P := fun h => Classical.choose (hdec0 h)
  have hdec : ∀ h : H, ∃ c : D.Cbar, (h : S.O) = (sf h : S.O) * (c : S.O) :=
    fun h => Classical.choose_spec (hdec0 h)
  let cf : H → D.Cbar := fun h => Classical.choose (hdec h)
  have hcf : ∀ h : H, (h : S.O) = (sf h : S.O) * (cf h : S.O) :=
    fun h => Classical.choose_spec (hdec h)
  have hcomm : ∀ (s : ↥P) (c : D.Cbar), (s : S.O) * (c : S.O) = (c : S.O) * (s : S.O) := by
    intro s c
    simpa using mem_centralizer_iff.mp c.2.2 (s : S.O) s.2
  have huniq : ∀ (s s' : ↥P) (c c' : D.Cbar),
      (s : S.O) * (c : S.O) = (s' : S.O) * (c' : S.O) → s = s' ∧ c = c' := by
    intro s s' c c' e
    have h1 : (s' : S.O)⁻¹ * (s : S.O) = (c' : S.O) * (c : S.O)⁻¹ := by
      calc (s' : S.O)⁻¹ * (s : S.O)
          = (s' : S.O)⁻¹ * ((s : S.O) * (c : S.O)) * (c : S.O)⁻¹ := by group
        _ = (s' : S.O)⁻¹ * ((s' : S.O) * (c' : S.O)) * (c : S.O)⁻¹ := by rw [e]
        _ = (c' : S.O) * (c : S.O)⁻¹ := by group
    have hP : (s' : S.O)⁻¹ * (s : S.O) ∈ P := P.mul_mem (P.inv_mem s'.2) s.2
    have hC : (s' : S.O)⁻¹ * (s : S.O) ∈ D.Cbar := by
      rw [h1]
      exact D.Cbar.mul_mem c'.2 (D.Cbar.inv_mem c.2)
    have hss : s' = s := Subtype.ext (inv_mul_eq_one.mp (D.eq_one_of_mem_sup_of_mem_Cbar hP hC))
    subst hss
    refine ⟨rfl, ?_⟩
    exact Subtype.ext (mul_left_cancel e)
  have hsf1 : sf 1 = 1 := by
    refine (huniq (sf 1) 1 (cf 1) 1 ?_).1
    rw [← hcf 1]
    simp
  have hsfmul : ∀ a b : H, sf (a * b) = sf a * sf b := by
    intro a b
    refine (huniq (sf (a * b)) (sf a * sf b) (cf (a * b)) (cf a * cf b) ?_).1
    have hcab : (cf a : S.O) * (sf b : S.O) = (sf b : S.O) * (cf a : S.O) :=
      (hcomm (sf b) (cf a)).symm
    calc (sf (a * b) : S.O) * (cf (a * b) : S.O) = ((a * b : H) : S.O) := (hcf (a * b)).symm
      _ = ((sf a : S.O) * (cf a : S.O)) * ((sf b : S.O) * (cf b : S.O)) := by
            rw [Subgroup.coe_mul, hcf a, hcf b]
      _ = ((sf a : S.O) * ((cf a : S.O) * (sf b : S.O))) * (cf b : S.O) := by group
      _ = ((sf a : S.O) * ((sf b : S.O) * (cf a : S.O))) * (cf b : S.O) := by rw [hcab]
      _ = ((sf a : S.O) * (sf b : S.O)) * ((cf a : S.O) * (cf b : S.O)) := by group
  let sfHom : H →* ↥P := { toFun := sf, map_one' := hsf1, map_mul' := hsfmul }
  have hker_le : Nat.card ↥sfHom.ker ≤ Nat.card ↥(H ⊓ D.Cbar) := by
    refine Nat.card_le_card_of_injective
      (fun h : ↥sfHom.ker => (⟨h.1.1, ⟨h.1.2, ?_⟩⟩ : ↥(H ⊓ D.Cbar))) ?_
    · have h1 : (h.1 : S.O) = (cf h.1 : S.O) := by
        rw [hcf h.1, show sf h.1 = 1 from h.2, OneMemClass.coe_one, one_mul]
      rw [h1]
      exact (cf h.1).2
    · intro h h' e
      exact Subtype.ext (Subtype.ext (by
        simpa using congrArg (fun z : ↥(H ⊓ D.Cbar) => (z.1 : S.O)) e))
  have hker_ge : Nat.card ↥(H ⊓ D.Cbar) ≤ Nat.card ↥sfHom.ker := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(H ⊓ D.Cbar) => (⟨⟨x.1, x.2.1⟩, ?_⟩ : ↥sfHom.ker)) ?_
    · show sf ⟨x.1, x.2.1⟩ = 1
      refine (huniq (sf ⟨x.1, x.2.1⟩) 1 (cf ⟨x.1, x.2.1⟩) ⟨x.1, x.2.2⟩ ?_).1
      rw [← hcf ⟨x.1, x.2.1⟩]
      simp
    · intro x x' e
      exact Subtype.ext (Subtype.ext (by
        simpa using congrArg (fun z : ↥sfHom.ker => (z.1.1 : S.O)) e))
  have hker : Nat.card ↥sfHom.ker = Nat.card ↥(H ⊓ D.Cbar) := le_antisymm hker_le hker_ge
  have hcardH : Nat.card H = Nat.card ↥sfHom.range * Nat.card ↥(H ⊓ D.Cbar) := by
    calc Nat.card H = Nat.card (H ⧸ sfHom.ker) * Nat.card ↥sfHom.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup sfHom.ker
      _ = Nat.card ↥sfHom.range * Nat.card ↥sfHom.ker := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange sfHom).toEquiv]
      _ = Nat.card ↥sfHom.range * Nat.card ↥(H ⊓ D.Cbar) := by rw [hker]
  have hQ2 : IsPGroup 2 ↥sfHom.range :=
    IsPGroup.of_surjective h2 sfHom.rangeRestrict (by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩)
  have hle2 : Nat.card ↥sfHom.range ≤ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hQ2
    have hdvd : 2 ^ n ∣ Nat.card ↥P := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card sfHom.range
    have h3dvd : 3 ∣ Nat.card ↥P := by
      have e : Nat.card ↥(D.Obar.subgroupOf P) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D.Obar ≤ P)).toEquiv,
          D.card_Obar]
      rw [← e]
      exact Subgroup.card_subgroup_dvd_card _
    have hPle : Nat.card ↥P ≤ 6 := D.card_Obar_sup_le_six
    obtain ⟨m, hm⟩ := h3dvd
    have hmle : m ≤ 2 := by omega
    have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by decide : Nat.Coprime 2 3)
    have hdn : 2 ^ n ∣ m := by
      apply hcop.dvd_of_dvd_mul_left
      rw [← hm]
      exact hdvd
    have hpos : 0 < m := by
      by_contra h
      push Not at h
      have : Nat.card ↥P = 0 := by omega
      have hPpos : 0 < Nat.card ↥P := Nat.card_pos
      omega
    have : 2 ^ n ≤ m := Nat.le_of_dvd hpos hdn
    omega
  calc Nat.card H = Nat.card ↥sfHom.range * Nat.card ↥(H ⊓ D.Cbar) := hcardH
    _ ≤ 2 * Nat.card ↥(H ⊓ D.Cbar) := Nat.mul_le_mul_right _ hle2

theorem card_le_four_mul_card_inf_Cbar_of_isPGroup {H : Subgroup S.O} (hH : H ≤ S.Mbar)
    (h2 : IsPGroup 2 H) :
    Nat.card H ≤ 4 * Nat.card (H ⊓ D.Cbar : Subgroup S.O) := by
  have hH1 : IsPGroup 2 ↥(H ⊓ M1) := h2.to_le inf_le_left
  have h2b := D.card_le_two_mul_card_inf_Cbar_of_isPGroup (M1 := M1) inf_le_right hH1
  have hCbar : (H ⊓ M1) ⊓ D.Cbar = H ⊓ D.Cbar := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, D.Cbar_le_M1 hx.2⟩, hx.2⟩
  rw [hCbar] at h2b
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  have hidx_dvd : M1.relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card M1 H
  rw [hn] at hidx_dvd
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx_dvd
  have hne : M1.relIndex S.Mbar ≠ 0 := by
    intro h0
    have hm := Subgroup.relIndex_mul_card M1 S.Mbar
    rw [h0, zero_mul] at hm
    have hpos : 0 < Nat.card ↥S.Mbar := Nat.card_pos
    omega
  have hidx_le : M1.relIndex H ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hH hne).trans D.rel.index_le
  have hidx2 : M1.relIndex H ≤ 2 := by
    rw [hk]
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have hmul := Subgroup.relIndex_mul_card M1 H
  rw [inf_comm M1 H] at hmul
  calc Nat.card H = M1.relIndex H * Nat.card ↥(H ⊓ M1) := hmul.symm
    _ ≤ 2 * Nat.card ↥(H ⊓ M1) := Nat.mul_le_mul_right _ hidx2
    _ ≤ 2 * (2 * Nat.card ↥(H ⊓ D.Cbar)) := Nat.mul_le_mul_left _ h2b
    _ = 4 * Nat.card ↥(H ⊓ D.Cbar) := by ring

private noncomputable def psiT (c : D.Cbar) : Vt S D.g D.t →ₗ[ZMod 2] S.Qt :=
  (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt) ∘ₗ
    LinearMap.prod LinearMap.id (LinearMap.id + ((ρV c : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t) :
      Vt S D.g D.t →ₗ[ZMod 2] Vt S D.g D.t))

private theorem psiT_apply (c : D.Cbar) (a : Vt S D.g D.t) :
    D.psiT c a = D.coord (a, a + ρV c a) := rfl

private theorem psiT_injective (c : D.Cbar) : Function.Injective (D.psiT c) := by
  intro a b h
  rw [psiT_apply, psiT_apply] at h
  exact (Prod.mk.inj (D.coord.injective h)).1

private theorem psiT_of_fixed (c : D.Cbar) {a : Vt S D.g D.t} (ha : ρV c a = a) :
    D.psiT c a = D.coord (a, 0) := by
  rw [psiT_apply, ha]
  congr 2
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem tc_apply_coord (c : D.Cbar) (u v : Vt S D.g D.t) :
    ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, v)) =
      D.coord (ρV c u + ρV c v, ρV c v) := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, D.Cbar_apply_coord, D.t_apply_coord]

private theorem add_self' (x : Vt S D.g D.t) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem mem_fixSpace_tc_iff {c : D.Cbar} (hcc : (c : S.O) * c = 1) {v : S.Qt} :
    v ∈ fixSpace ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      ∃ a : Vt S D.g D.t, v = D.psiT c a := by
  obtain ⟨⟨u, w⟩, rfl⟩ := D.coord.surjective v
  have hc2 : ∀ a, ρV c (ρV c a) = a := D.resC_resC_apply hcc
  rw [mem_fixSpace, tc_apply_coord]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj (D.coord.injective h)
    refine ⟨u, ?_⟩
    rw [psiT_apply]
    have h3 : ρV c w = u - ρV c u := eq_sub_of_add_eq' h1
    have : w = u + ρV c u := by rw [← h2, h3, sub_eq_add_vec (ZMod 2)]
    rw [this]
  · rintro ⟨a, ha⟩
    rw [psiT_apply] at ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.coord.injective ha)
    rw [map_add, hc2]
    congr 1
    refine Prod.ext ?_ ?_
    · show ρV c u + (ρV c u + u) = u
      rw [← add_assoc, D.add_self', zero_add]
    · show ρV c u + u = u + ρV c u
      exact add_comm _ _

private theorem commSpace_tc_eq {c : D.Cbar} (hcc : (c : S.O) * c = 1) :
    commSpace ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      fixSpace ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hc2 : ∀ a, ρV c (ρV c a) = a := D.resC_resC_apply hcc
  have htt' : (D.t * (c : S.O)) * (D.t * (c : S.O)) = 1 := by
    have hct : (c : S.O) * D.t = D.t * c := D.comm_of_mem_Cbar c.2
    calc (D.t * (c : S.O)) * (D.t * (c : S.O)) = D.t * ((c : S.O) * D.t) * c := by group
      _ = D.t * (D.t * c) * c := by rw [hct]
      _ = (D.t * D.t) * ((c : S.O) * c) := by group
      _ = 1 := by rw [D.t_mul_t, hcc, one_mul]
  have htt : ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      ((D.t * (c : S.O) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    rw [← Subgroup.coe_mul, htt']
    rfl
  refine le_antisymm (commSpace_le_fixSpace htt) fun v hv => ?_
  obtain ⟨a, rfl⟩ := (D.mem_fixSpace_tc_iff hcc).mp hv
  refine mem_commSpace.mpr ⟨D.coord (0, ρV c a), ?_⟩
  rw [tc_apply_coord, map_zero, zero_add, hc2, psiT_apply, ← map_sub]
  congr 1
  refine Prod.ext ?_ ?_
  · show a - 0 = a
    rw [sub_zero]
  · show a - ρV c a = a + ρV c a
    rw [sub_eq_add_vec (ZMod 2)]

theorem Dl_ne_bot_of_eq_t_mul {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG)
    {c : D.Cbar} (hcc : (c : S.O) * c = 1) (hx : S.ρ ⟨_, hxM⟩ = D.t * (c : S.O)) :
    S.QG ⊓ S.Qa k ≠ ⊥ := by
  intro hbot
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hfixQ : ∀ v, v ∈ S.fixQt (k * S.z * k⁻¹) ↔ ∃ a, v = D.psiT c a := by
    intro v
    rw [S.fixQt_of_mem hxM, hx]
    exact D.mem_fixSpace_tc_iff hcc
  have hinj : ∀ g₁ (h₁ : g₁ ∈ S.L0 k) g₂ (h₂ : g₂ ∈ S.L0 k),
      S.ρ ⟨g₁, h₁.2⟩ = S.ρ ⟨g₂, h₂.2⟩ → g₁ = g₂ := by
    intro g₁ h₁ g₂ h₂ e
    have hm : g₁⁻¹ * g₂ ∈ S.L0 k := (S.L0 k).mul_mem ((S.L0 k).inv_mem h₁) h₂
    have hρ : S.ρ ⟨g₁⁻¹ * g₂, hm.2⟩ = 1 := by
      have : (⟨g₁⁻¹ * g₂, hm.2⟩ : S.M) = (⟨g₁, h₁.2⟩ : S.M)⁻¹ * ⟨g₂, h₂.2⟩ := rfl
      rw [this, map_mul, map_inv, e, inv_mul_cancel]
    have hQ : g₁⁻¹ * g₂ ∈ S.QG := (S.ρ_eq_one_iff _).mp hρ
    have hΔ : g₁⁻¹ * g₂ ∈ S.QG ⊓ S.Qa k := ⟨hQ, hm.1⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hΔ
    exact hΔ
  have hLM : S.Lbar k ≤ S.Mbar := Subgroup.map_le_range _ _
  have hcardL : 2 ^ S.width ≤ Nat.card (S.Lbar k) := by
    refine (SMK.card_L0_ge S hxM hxQ).trans (Nat.card_le_card_of_injective
      (fun g : S.L0 k => (⟨S.ρ ⟨g, g.2.2⟩, ⟨⟨g, g.2.2⟩, mem_subgroupOf.mpr g.2, rfl⟩⟩ :
        S.Lbar k)) fun g₁ g₂ e => Subtype.ext (hinj _ g₁.2 _ g₂.2 (congrArg Subtype.val e)))
  have hLfix : ∀ ℓ ∈ S.Lbar k, ∀ v ∈ S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)),
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    rintro ℓ ⟨m, hm, rfl⟩ v hv
    obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hv
    have hmL : (m : G) ∈ S.L0 k := mem_subgroupOf.mp hm
    have hcomm := SMK.commutator_mem_Dl S hmL hu
    rw [hbot, Subgroup.mem_bot] at hcomm
    have : (m : G) * u * (m : G)⁻¹ = u := by
      rw [mul_inv_eq_one] at hcomm
      exact hcomm
    rw [S.ρ_cl m huQ, this]
  set C := S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) with hC
  have hCle : C ≤ LinearMap.range (D.psiT c) := fun v hv => by
    obtain ⟨a, rfl⟩ := (hfixQ v).mp (S.clSub_centralizer_le_fixQt hxM hv)
    exact ⟨a, rfl⟩
  set A := C.comap (D.psiT c) with hA
  have hfr : finrank (ZMod 2) (S.fixQt (k * S.z * k⁻¹)) = S.width := by
    have : S.fixQt (k * S.z * k⁻¹) = LinearMap.range (D.psiT c) := by
      ext v
      rw [hfixQ, LinearMap.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
    rw [this, LinearMap.finrank_range_of_inj (D.psiT_injective c), D.finrank_Vt]
  have hAC : finrank (ZMod 2) A = finrank (ZMod 2) C := by
    have h1 : A.map (D.psiT c) = C := Submodule.map_comap_eq_of_le hCle
    rw [← h1]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (D.psiT_injective c) A))
  have hAdim : finrank (ZMod 2) (Vt S D.g D.t) ≤ finrank (ZMod 2) A + 1 := by
    have := SMK.finrank_fixQt_le S hxM hxQ hx2
    rw [hfr, ← hC, ← hAC] at this
    rw [D.finrank_Vt]
    exact this
  set H' : Subgroup (Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t) :=
    ((S.Lbar k ⊓ D.Cbar).subgroupOf D.Cbar).map (ρV) with hH'
  have hH'2 : Nat.card H' ≤ 2 := by
    refine card_le_two_of_forall_apply_eq D.QV_nondegenerate hAdim H' ?_ ?_
    · rintro e ⟨ℓ, -, rfl⟩ v
      exact D.QV_resC ℓ v
    · rintro e ⟨ℓ, hℓ, rfl⟩ a ha
      have hℓL : (ℓ : S.O) ∈ S.Lbar k := (mem_subgroupOf.mp hℓ).1
      have h1 := hLfix ℓ hℓL (D.psiT c a) ha
      rw [psiT_apply, D.Cbar_apply_coord] at h1
      exact (Prod.mk.inj (D.coord.injective h1)).1
  have hcardC : Nat.card (S.Lbar k ⊓ D.Cbar : Subgroup S.O) ≤ 2 := by
    have e1 : Nat.card H' = Nat.card ((S.Lbar k ⊓ D.Cbar).subgroupOf D.Cbar) :=
      Subgroup.card_map_of_injective D.resC_injective
    have e2 : Nat.card ((S.Lbar k ⊓ D.Cbar).subgroupOf D.Cbar) =
        Nat.card (S.Lbar k ⊓ D.Cbar : Subgroup S.O) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [← e2, ← e1]
    exact hH'2
  have h12 := (D.card_le_four_mul_card_inf_Cbar_of_isPGroup hLM
    (S14.SMK.isPGroup_Lbar S k)).trans (Nat.mul_le_mul_left 4 hcardC)
  have h64 : 2 ^ 4 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) D.four_le
  have := hcardL.trans h12
  omega

theorem not_bad_of_eq_t_mul {k : G} (hbad : Bad S k) {c : D.Cbar}
    (hcc : (c : S.O) * c = 1) (hx : S.ρ ⟨_, hbad.mem_M⟩ = D.t * (c : S.O)) : False := by
  have hxM := hbad.mem_M
  have hxQ := hbad.not_mem_QG
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hΔ := D.Dl_ne_bot_of_eq_t_mul hxM hxQ hcc hx
  have hfixQ : ∀ v, v ∈ S.fixQt (k * S.z * k⁻¹) ↔ ∃ a, v = D.psiT c a := by
    intro v
    rw [S.fixQt_of_mem hxM, hx]
    exact D.mem_fixSpace_tc_iff hcc
  have hcomm_eq : S.commQt (k * S.z * k⁻¹) = S.fixQt (k * S.z * k⁻¹) := by
    rw [S.commQt_of_mem hxM, S.fixQt_of_mem hxM, hx]
    exact D.commSpace_tc_eq hcc
  have hΔfix : S.clSub (S.QG ⊓ S.Qa k) ≤ S.fixQt (k * S.z * k⁻¹) :=
    (S.clSub_mono (SMK.Dl_le_Kz S)).trans (S.clSub_centralizer_le_fixQt hxM)
  obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΔ
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdz : d ≠ S.z := fun e => SMK.z_not_mem_Dl S hxQ (e ▸ hd)
  by_cases hxz : IsConj S.z (k * S.z * k⁻¹ * S.z)
  ·
    have hdJ : d ∈ (⁅zpowers (k * S.z * k⁻¹), S.QG⁆ : Subgroup G) := by
      rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2]
      refine ⟨hd.1, ?_⟩
      rw [hcomm_eq]
      exact hΔfix (S.cl_mem_clSub hd hd.1)
    have hdx : Commute (k * S.z * k⁻¹) d :=
      (mem_centralizer_singleton_iff.mp (SMK.mem_centralizer_of_mem_Qa S hd.2)).symm
    rcases SMF.isConj_of_mem_J S hxM hxQ hd1' hdJ hdx hd.2 with h | h
    · exact hbad.not_mem h hd
    · exact hbad.not_mem (hxz.trans h) hd
  · have hfix := SMK.fixQt_eq_of_not_isConj S hxM hxz
    have hc2 : ∀ a, ρV c (ρV c a) = a := D.resC_resC_apply hcc
    have hqψ : ∀ a, D.betaV a (ρV c a) = 0 := by
      intro a
      have hmem : D.psiT c a ∈ S.fixQt (k * S.z * k⁻¹) := (hfixQ _).mpr ⟨a, rfl⟩
      have h0 := q_eq_zero_of_mem_commQt_of_mem_clSub hxM hx2 (hcomm_eq ▸ hmem) (hfix ▸ hmem)
      rw [psiT_apply, D.q_coord, map_add, D.betaV_isAlt a, zero_add] at h0
      exact h0
    have hA : ∀ y ∈ commSpace (ρV c), D.QV y = 0 := by
      intro y hy
      obtain ⟨a, rfl⟩ := mem_commSpace.mp hy
      rw [sub_eq_add_vec (ZMod 2), QuadraticMap.map_add D.QV, D.QV_resC, D.polar_QV,
        D.betaV_symm, hqψ, add_zero]
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    have huu : ρV c * ρV c = 1 := LinearEquiv.ext fun a => by
      rw [LinearEquiv.mul_apply, hc2]
      rfl
    set U := (S.clSub (S.QG ⊓ S.Qa k)).comap (D.psiT c) with hU
    have hU0 : U ≠ ⊥ := by
      obtain ⟨a, ha⟩ := (hfixQ _).mp (hΔfix (S.cl_mem_clSub hd hd.1))
      intro hbot
      have haU : a ∈ U := by
        show D.psiT c a ∈ S.clSub (S.QG ⊓ S.Qa k)
        rw [← ha]
        exact S.cl_mem_clSub hd hd.1
      rw [hbot, Submodule.mem_bot] at haU
      rw [haU, map_zero] at ha
      rcases (S.cl_eq_zero_iff hd.1).mp ha with e | e
      · exact hd1' e
      · exact hdz e
    have hUinv : ∀ e f : Vt S D.g D.t, D.QV e = 0 → polar D.QV e f = 0 →
        eichler D.QV e f * ρV c = ρV c * eichler D.QV e f → ∀ v ∈ U, eichler D.QV e f v ∈ U := by
      intro e f _ _ hEc v hv
      obtain ⟨cE, hcE⟩ := D.exists_Cbar_resC_eq_eichler e f
      have hcEc : cE * c = c * cE := D.resC_injective (by rw [map_mul, map_mul, hcE, hEc])
      have hcEc' : (cE : S.O) * c = c * cE := congrArg Subtype.val hcEc
      have hcEt : (cE : S.O) * D.t = D.t * cE := D.comm_of_mem_Cbar cE.2
      have hyx : (cE : S.O) * S.ρ ⟨_, hxM⟩ = S.ρ ⟨_, hxM⟩ * cE := by
        rw [hx]
        calc (cE : S.O) * (D.t * c) = ((cE : S.O) * D.t) * c := by group
          _ = D.t * ((cE : S.O) * c) := by rw [hcEt]; group
          _ = D.t * c * cE := by rw [hcEc']; group
      have h1 := clSub_Dl_apply_mem hxM hxz (D.Cbar_le_Mbar cE.2) hyx hv
      show D.psiT c (eichler D.QV e f v) ∈ S.clSub (S.QG ⊓ S.Qa k)
      have h2 : ((cE : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.psiT c v) =
          D.psiT c (eichler D.QV e f v) := by
        rw [psiT_apply, psiT_apply, D.Cbar_apply_coord, hcE, map_add]
        congr 2
        have := congrArg (fun φ : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t => φ v) hEc
        simp only [LinearEquiv.mul_apply] at this
        rw [this]
      rw [← h2]
      exact h1
    have h3 : 3 ≤ finrank (ZMod 2) (Vt S D.g D.t) := by
      rw [D.finrank_Vt]
      have := D.four_le
      omega
    obtain ⟨p, hpU, hp0, hpQ, hpc⟩ := exists_singular_fixed_of_invariant D.QV_nondegenerate h3
      (D.QV_resC c) huu hA ⟨aV D.good.ht, S4.aV_ne_zero D.good.H D.good.ht, D.QV_aV⟩ hU0 hUinv
    have hpΔ : D.coord (p, 0) ∈ S.clSub (S.QG ⊓ S.Qa k) := by
      have h2 : D.psiT c p ∈ S.clSub (S.QG ⊓ S.Qa k) := Submodule.mem_comap.mp hpU
      rwa [D.psiT_of_fixed c hpc] at h2
    obtain ⟨d', hd'Δ, hd'Q, hcl⟩ := S.mem_clSub_iff.mp hpΔ
    have hd'z : d' ≠ S.z := fun e => SMK.z_not_mem_Dl S hxQ (e ▸ hd'Δ)
    exact hbad.not_mem ((D.isConj_z_iff_coord hd'Q hd'z).mpr ⟨p, hp0, hpQ, Or.inl hcl⟩) hd'Δ

theorem not_bad_of_not_mem_Cbar_of_mem_M1 {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hx1 : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∈ M1)
    (hxC : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∉ D.Cbar) : ¬ Bad S k := by
  intro hbad
  have hxx : S.ρ ⟨_, hxM⟩ * S.ρ ⟨_, hxM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨_, hxM⟩ : S.M) * ⟨_, hxM⟩ = 1 := Subtype.ext (by
      show k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1
      calc k * S.z * k⁻¹ * (k * S.z * k⁻¹) = k * (S.z * S.z) * k⁻¹ := by group
        _ = 1 := by rw [S.z_mul_z, mul_one, mul_inv_cancel])
    rw [this, map_one]
  obtain ⟨s, c, hs, hcc, hx⟩ := D.exists_eq_mul_of_mul_self_eq_one_of_mem_M1 hx1 hxx
  rcases hs with rfl | hT
  · exact hxC (by rw [hx, one_mul]; exact c.2)
  obtain ⟨m₁, hm₁⟩ := MonoidHom.mem_range.mp D.k_mem_Mbar
  have htk0 : D.t * D.k⁻¹ * D.t⁻¹ = D.k := by
    calc D.t * D.k⁻¹ * D.t⁻¹ = (D.t * D.k * D.t⁻¹)⁻¹ := by group
      _ = D.k := by rw [D.t_inv, inv_inv]
  have htk : D.t * D.k⁻¹ = D.k * D.t := by
    calc D.t * D.k⁻¹ = (D.t * D.k⁻¹ * D.t⁻¹) * D.t := by group
      _ = D.k * D.t := by rw [htk0]
  have hk3 : D.k * D.k * D.k = 1 := by
    have := D.k_cube
    rwa [pow_three, ← mul_assoc] at this
  have hck : (c : S.O) * D.k = D.k * c :=
    ((mem_centralizer_iff.mp (c.2 : (c : S.O) ∈ D.Cbar).2) D.k
      (Subgroup.mem_sup_left D.k_mem_Obar)).symm
  obtain ⟨m, hm, hcm⟩ : ∃ m : S.M, S.ρ m * s * (S.ρ m)⁻¹ = D.t ∧ (c : S.O) * S.ρ m = S.ρ m * c := by
    rcases hT with rfl | rfl | rfl
    · exact ⟨1, by rw [map_one, one_mul, inv_one, mul_one], by rw [map_one, one_mul, mul_one]⟩
    · refine ⟨m₁, ?_, by rw [hm₁, hck]⟩
      rw [hm₁]
      calc D.k * (D.k * D.t) * D.k⁻¹ = D.k * D.k * (D.t * D.k⁻¹) := by group
        _ = D.k * D.k * (D.k * D.t) := by rw [htk]
        _ = (D.k * D.k * D.k) * D.t := by group
        _ = D.t := by rw [hk3, one_mul]
    · refine ⟨m₁ * m₁, ?_, ?_⟩
      · rw [map_mul, hm₁]
        calc D.k * D.k * (D.k * D.k * D.t) * (D.k * D.k)⁻¹ =
            D.k * D.k * D.k * D.k * (D.t * D.k⁻¹) * D.k⁻¹ := by group
          _ = D.k * D.k * D.k * D.k * (D.k * D.t) * D.k⁻¹ := by rw [htk]
          _ = D.k * D.k * D.k * D.k * D.k * (D.t * D.k⁻¹) := by group
          _ = D.k * D.k * D.k * D.k * D.k * (D.k * D.t) := by rw [htk]
          _ = (D.k * D.k * D.k) * (D.k * D.k * D.k) * D.t := by group
          _ = D.t := by rw [hk3, one_mul, one_mul]
      · rw [map_mul, hm₁, ← mul_assoc, hck, mul_assoc, hck, mul_assoc]
  have hbad' := hbad.mul_left m.2
  have hx' : S.ρ ⟨_, hbad'.mem_M⟩ = D.t * (c : S.O) := by
    have e : (⟨(m : G) * k * S.z * ((m : G) * k)⁻¹, hbad'.mem_M⟩ : S.M) =
        m * ⟨_, hxM⟩ * m⁻¹ := Subtype.ext (by
      show (m : G) * k * S.z * ((m : G) * k)⁻¹ = (m : G) * (k * S.z * k⁻¹) * (m : G)⁻¹
      group)
    have hcm' : S.ρ m * (c : S.O) * (S.ρ m)⁻¹ = c := by
      rw [← hcm]
      group
    rw [e, map_mul, map_mul, map_inv, hx]
    calc S.ρ m * (s * c) * (S.ρ m)⁻¹ =
        (S.ρ m * s * (S.ρ m)⁻¹) * (S.ρ m * (c : S.O) * (S.ρ m)⁻¹) := by group
      _ = D.t * c := by rw [hm, hcm']
  exact D.not_bad_of_eq_t_mul hbad' hcc hx'

end Rel

section Full

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem not_bad_of_not_mem_Cbar {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hxC : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ ∉ D.Cbar) : ¬ Bad S k :=
  D.not_bad_of_not_mem_Cbar_of_mem_M1 hxM (MonoidHom.mem_range.mpr ⟨_, rfl⟩) hxC

end Full

end S2Data

end CFSG.GF2Type.Smith1980Orth
