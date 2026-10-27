module

public import CFSG.LargeExtraspecial.DW3CaseIIMbar
public import CFSG.LargeExtraspecial.DWCaseIIBSLA
public import CFSG.LargeExtraspecial.DWCaseIIBSp
public import CFSG.LargeExtraspecial.TSComplExtend
public import CFSG.LargeExtraspecial.GLW4Dnu

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GroupTheory

open MulAction

theorem exists_involution_mem_stabilizer_of_card_orbit_lt {Γ X : Type*} [Group Γ] [Finite Γ]
    [MulAction Γ X] {b : X} (h8 : 8 ∣ Nat.card Γ)
    (hlt : Nat.card (MulAction.orbit Γ b) < 8) :
    ∃ t ∈ MulAction.stabilizer Γ b, t ≠ 1 ∧ t * t = 1 := by
  classical
  have hindex : (MulAction.stabilizer Γ b).index = Nat.card (MulAction.orbit Γ b) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hmul : Nat.card (MulAction.stabilizer Γ b) * Nat.card (MulAction.orbit Γ b) =
      Nat.card Γ := by
    rw [← hindex]
    exact (MulAction.stabilizer Γ b).card_mul_index
  have hdv : 8 ∣ Nat.card (MulAction.stabilizer Γ b) * Nat.card (MulAction.orbit Γ b) := by
    rw [hmul]
    exact h8
  have h2 : 2 ∣ Nat.card (MulAction.stabilizer Γ b) := by
    by_contra hnot
    have hodd : Odd (Nat.card (MulAction.stabilizer Γ b)) :=
      Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    have hcop : Nat.Coprime 8 (Nat.card (MulAction.stabilizer Γ b)) := by
      have h2cop : Nat.Coprime 2 (Nat.card (MulAction.stabilizer Γ b)) :=
        Nat.coprime_two_left.mpr hodd
      simpa using h2cop.pow_left 3
    have hdvorbit : 8 ∣ Nat.card (MulAction.orbit Γ b) :=
      hcop.dvd_of_dvd_mul_left hdv
    haveI : Finite (MulAction.orbit Γ b) :=
      Finite.of_surjective
        (fun g : Γ => (⟨g • b, MulAction.mem_orbit b g⟩ : MulAction.orbit Γ b))
        (by
          rintro ⟨x, hx⟩
          obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
          exact ⟨g, rfl⟩)
    haveI : Nonempty (MulAction.orbit Γ b) :=
      ⟨⟨b, MulAction.mem_orbit_self b⟩⟩
    have hpos : 0 < Nat.card (MulAction.orbit Γ b) := Nat.card_pos
    have hge : 8 ≤ Nat.card (MulAction.orbit Γ b) := Nat.le_of_dvd hpos hdvorbit
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer Γ b) 2 h2
  have htco : orderOf (t : Γ) = 2 := (Subgroup.orderOf_coe t).trans ht
  refine ⟨(t : Γ), t.2, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at htco
    omega
  · have hpow : (t : Γ) ^ 2 = 1 := by
      rw [← htco]
      exact pow_orderOf_eq_one (t : Γ)
    simpa [pow_two] using hpow

end CFSG.GroupTheory

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open CFSG.LargeExtraspecial.GLW4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

private theorem false_of_isAlt_nondegenerate_finrank_three
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ω : LinearMap.BilinForm K V} (hnd : ω.Nondegenerate) (halt : ω.IsAlt)
    (h3 : finrank K V = 3) : False := by
  have hev := LinearMap.BilinForm.IsAlt.even_finrank halt hnd
  rw [h3] at hev
  obtain ⟨k, hk⟩ := hev
  omega

theorem false_of_sl_of_noInvariantCompl (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) (hw : S.width = 3)
    (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
    (hD : spanD S = S.clSub A)
    (hsl : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z →
      axisA S A g = ZMod 2 ∙ S.cl (g * S.z * g⁻¹))
    (hNS : ∀ B : Submodule (ZMod 2) S.Qt, IsMbarInvariant S B → (∀ b ∈ B, S.q b = 0) →
      ¬ IsCompl (S.clSub A) B)
    {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z) : False := by
  classical
  have hxQ : g * S.z * g⁻¹ ∈ S.QG := hA.le_QG hxA
  set xT : S.Qt := S.cl (g * S.z * g⁻¹) with hxT
  have hx0 : xT ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hxU : xT ∈ S.clSub A := S.cl_mem_clSub hxA hxQ
  have hsurj : Function.Surjective (resAt S A hM) :=
    hA.resAt_surjective_of_axisA_eq hM hII hD hsl
  let P : Subgroup S.Mbar := stabMbar S xT
  have hPcard : Nat.card P = 24 := hA.card_stabilizer_eq hM hw hsurj hxU hx0
  let U : Submodule (ZMod 2) S.Qt := S.clSub A
  let W : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa g)
  haveI : FiniteDimensional (ZMod 2) S.Qt := finiteDimensional_Qt
  have hE : finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hU3 : finrank (ZMod 2) U = 3 := by
    dsimp [U]
    rw [hA.finrank_clSub, hw]
  have hUq : ∀ u ∈ U, S.q u = 0 := fun u hu => q_clSub hu
  have hW3 : finrank (ZMod 2) W = 3 := by
    dsimp [W]
    rw [hA.finrank_clSub_E hM hII hbad hD hxA hxz, hw]
  have hWq : ∀ w ∈ W, S.q w = 0 := by
    intro w hw
    dsimp [W] at hw
    obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hw
    exact (S.q_cl_eq_zero_iff heQ).mpr (S.QG_inf_Qa_sq hxz he)
  have hWU : W ⊓ U = Submodule.span (ZMod 2) {xT} := by
    refine le_antisymm ?_ ?_
    · intro v hv
      dsimp [W, U] at hv
      have := hA.mem_span_of_mem_clSub_E hM hII (hsl g hxA hxz) hv.2 hv.1
      simpa [xT] using this
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨by simpa [W, xT] using S.cl_mem_clSub (hA.conj_mem_E hxA) hxQ, hxU⟩
  obtain ⟨B₁, hB₁, hB₁le⟩ :=
    exists_mem_tsCompl_inf_le (E := S.Qt) (q := S.q) S.q_nondegenerate hE hU3 hUq hxU hx0
      hW3 hWq hWU
  obtain ⟨B₂, hB₂, hB₂nle⟩ :=
    exists_mem_tsCompl_not_inf_le (E := S.Qt) (q := S.q) S.q_nondegenerate hE hU3 hUq hxU hx0
      hW3 hWq hWU
  have hcardC : Nat.card (tsCompl S.q U) = 8 :=
    card_tsCompl_eq_eight S.q_nondegenerate hB₁.1 hUq hB₁.2 hU3
  let Pperp : Submodule (ZMod 2) S.Qt :=
    LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ xT)
  let Cw : Set (tsCompl S.q U) := {B | B.1 ⊓ Pperp ≤ W}
  have hfixP : ∀ p : P, ((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) xT = xT :=
    fun p => mem_stabMbar.mp p.2
  have hWpres : ∀ (p : P) {v : S.Qt}, v ∈ W →
      ((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W := by
    intro p v hv
    obtain ⟨m, hm⟩ := (((p : P) : S.Mbar)).2
    have hfix : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) xT = xT := by
      simpa [hm] using hfixP p
    have hmem := apply_mem_clSub_inf (S := S) (g := g) hxQ hxz m.2 hfix hv
    simpa [hm] using hmem
  have hWmap : ∀ p : P,
      W.map (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
        S.Qt →ₗ[ZMod 2] S.Qt) = W := by
    intro p
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro v ⟨w, hw, rfl⟩
      exact hWpres p hw
    · rw [LinearEquiv.finrank_map_eq]
  have hPperp_map : ∀ p : P,
      Pperp.map (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
        S.Qt →ₗ[ZMod 2] S.Qt) = Pperp := by
    intro p
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro z ⟨v, hv, rfl⟩
      dsimp only [Pperp] at hv ⊢
      change v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ xT) at hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change polar S.q (c • xT) (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0
      rw [polar_smul_left]
      have hsymm :
          (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).symm xT = xT := by
        calc (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).symm xT
            = (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).symm
                ((((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) xT) := by
                rw [hfixP p]
          _ = xT := LinearEquiv.symm_apply_apply _ _
      have h1 := polar_apply_apply (((p : P) : S.Mbar) : S.O)
        ((((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).symm xT) v
      rw [LinearEquiv.apply_symm_apply, hsymm] at h1
      rw [h1]
      have hvx : polar (⇑S.q) xT v = 0 := by
        simpa only [polarBilin_apply_apply] using hv xT (Submodule.mem_span_singleton_self xT)
      rw [hvx, smul_zero]
    · rw [LinearEquiv.finrank_map_eq]
  haveI hSubFin : Finite (Submodule (ZMod 2) S.Qt) :=
    Finite.of_injective (fun V : Submodule (ZMod 2) S.Qt => (V : Set S.Qt))
      SetLike.coe_injective
  haveI : Finite (tsCompl S.q U) := inferInstance
  letI : MulAction S.Mbar (tsCompl S.q U) := tsComplAction (S := S) (A := A) hM
  letI : MulAction P (tsCompl S.q U) := MulAction.compHom (tsCompl S.q U) P.subtype
  have hCw_smul : ∀ (p : P) (B : tsCompl S.q U), B ∈ Cw → p • B ∈ Cw := by
    intro p B hB
    have hB' : B.1 ⊓ Pperp ≤ W := hB
    have hmapinf :
        B.1.map (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
            S.Qt →ₗ[ZMod 2] S.Qt) ⊓ Pperp =
          (B.1 ⊓ Pperp).map (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
            S.Qt →ₗ[ZMod 2] S.Qt) := by
      rw [Submodule.map_inf _
        (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)).injective, hPperp_map p]
    change B.1.map (((((p : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
      S.Qt →ₗ[ZMod 2] S.Qt) ⊓ Pperp ≤ W
    rw [hmapinf]
    exact (Submodule.map_mono hB').trans (le_of_eq (hWmap p))
  let B₁t : tsCompl S.q U := ⟨B₁, hB₁⟩
  let B₂t : tsCompl S.q U := ⟨B₂, hB₂⟩
  have hB₁cw : B₁t ∈ Cw := hB₁le
  have hB₂ncw : B₂t ∉ Cw := hB₂nle
  have horb_subset : ∀ B ∈ MulAction.orbit P B₁t, B ∈ Cw := by
    rintro B ⟨p, rfl⟩
    exact hCw_smul p B₁t hB₁cw
  have hCwlt : Nat.card Cw < 8 := by
    have hproper : Cw ⊂ (Set.univ : Set (tsCompl S.q U)) := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
      intro h
      exact hB₂ncw (by rw [h]; exact Set.mem_univ B₂t)
    have hlt := Set.ncard_lt_ncard hproper (Set.toFinite _)
    rw [Set.ncard_univ, hcardC] at hlt
    rwa [← Nat.card_coe_set_eq Cw] at hlt
  have horb_le : Nat.card (MulAction.orbit P B₁t) ≤ Nat.card Cw := by
    refine Nat.card_le_card_of_injective
      (f := fun x : MulAction.orbit P B₁t => (⟨x.1, horb_subset x.1 x.2⟩ : Cw)) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : Cw => z.1) hab)
  have horb_lt : Nat.card (MulAction.orbit P B₁t) < 8 := by
    have hle : Nat.card (MulAction.orbit P B₁t) ≤ 7 :=
      (le_trans horb_le (by omega))
    omega
  haveI hPfin : Finite P :=
    Finite.of_injective (fun p : P => (((p : P) : S.Mbar))) (fun a b h => Subtype.ext h)
  have h8P : 8 ∣ Nat.card P := by rw [hPcard]; norm_num
  obtain ⟨t, htmem, ht1, ht2⟩ :=
    CFSG.GroupTheory.exists_involution_mem_stabilizer_of_card_orbit_lt
      (Γ := P) (X := tsCompl S.q U) (b := B₁t) h8P horb_lt
  have htfix : t • B₁t = B₁t := MulAction.mem_stabilizer_iff.mp htmem
  have hmap : Submodule.map (((((t : P) : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
      S.Qt →ₗ[ZMod 2] S.Qt) B₁ = B₁ := by
    show (t • B₁t).1 = B₁t.1
    exact congrArg Subtype.val htfix
  have ht1' : (((t : P) : S.Mbar)) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2' : (((t : P) : S.Mbar)) * (((t : P) : S.Mbar)) = 1 := by
    have := congrArg (fun x : P => (((x : P) : S.Mbar))) ht2
    simpa using this
  exact (hA.map_ne_of_noInvariantCompl hM hw hsurj hNS ht1' ht2' hB₁) hmap

theorem false_of_bad_of_noInvariantCompl (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) (hw : S.width = 3)
    (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
    (hNS : ∀ B : Submodule (ZMod 2) S.Qt, IsMbarInvariant S B → (∀ b ∈ B, S.q b = 0) →
      ¬ IsCompl (S.clSub A) B)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z) : False := by
  have hWs := q_spanD hII
  have hD := hA.spanD_eq_clSub hM hII hg₀A hg₀z (by omega) hbad
  rcases hA.finrank_axisD_le_one_or hM hII hbad hg₀A hg₀z with hsl | hsp
  · have hslall : ∀ h : G, h * S.z * h⁻¹ ∈ A → h * S.z * h⁻¹ ≠ S.z →
        axisA S A h = ZMod 2 ∙ S.cl (h * S.z * h⁻¹) := by
      intro h hhA hhz
      have hhQ := hA.le_QG hhA
      have hdim := finrank_axisD_eq hWs hhQ hhz (hA.le_QG hg₀A) hg₀z
      have hax : axisD S h = axisA S A h := by
        rw [hA.axisD_eq hII hhA hhz, hD]
        exact inf_eq_left.mpr (S.clSub_mono inf_le_left)
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (hA.cl_mem_axisA hhA)) ?_).symm
      rw [finrank_span_singleton ((cl_ne_zero_iff hhQ).mpr hhz), ← hax, hdim]
      exact hsl
    exact hA.false_of_sl_of_noInvariantCompl hM hII hw hbad hD hslall hNS hg₀A hg₀z
  · obtain ⟨ω, hnd, halt, -⟩ :=
      hA.spConfig_of_hyp hM hII hbad (by omega) hg₀A hg₀z hsp
    exact false_of_isAlt_nondegenerate_finrank_three hnd halt (by
      rw [hA.finrank_clSub, hw])

end MaxEA

end CFSG.LargeExtraspecial.DW
