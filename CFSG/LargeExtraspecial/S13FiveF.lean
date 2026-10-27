module

public import CFSG.LargeExtraspecial.S13FiveE
public import CFSG.LargeExtraspecial.S13EntryB
public import CFSG.LargeExtraspecial.S13FiveC
public import CFSG.LargeExtraspecial.S13FiveD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

theorem pf_act_Γ₁ : ∀ γ : Gm, γ.2 = 1 → pf E00 (act γ E00) = 0 := by decide +kernel

theorem act_Γ₁_add : ∀ γ : Gm, γ.2 ≠ 1 ∨ act γ E00 = E00 ∨
    ∃ δ : Gm, δ.2 = 1 ∧ act δ E00 = E00 + act γ E00 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem mem_Lbar_mul_of_commute {s : S.O} (hs : s ∈ S.Lbar g) {m : S.M}
    (hc : S.ρ m * s = s * S.ρ m) : s ∈ S.Lbar ((m : G) * g) := by
  have h1 := conj_mem_Lbar_mul S m hs
  rwa [hc, mul_inv_cancel_right] at h1

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem K_ne_bot : K ≠ ⊥ := by
  intro h
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  rw [h, mem_bot] at hk
  exact hk1 hk

theorem isPGroup_K : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by rw [Y.card_K, pow_one])

omit Y in
theorem timmesfeld_13_5
    (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K)
    (hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K → Rbar S g τ = S.Lbar g ∨ LinCase S g hτ) :
    ∃ σ, ∃ hσ : σ ∈ S.Lbar g, σ ∉ Ebar S g K ∧ LinCase S g hσ ∧
      3 ≤ finrank (ZMod 2) (Vt S g σ) := by
  obtain ⟨t, X, hNK, -, k, hkN, hkA, hkt⟩ := Y.sec10
  have h7 := Y.seven_le
  obtain ⟨Xb, Yb, D⟩ := exists_dec108 hCE X ⟨k, (Subgroup.mem_inf.mp hkA).1, hkt⟩ h7
  have hE : Ebar S g K = S.Lbar g ⊓ Xb :=
    Ebar_eq_of Y.K_le Y.K_ne_bot Y.isPGroup_K Y.normal X h7 Y.irr hCE D
  have hKR : K ≤ Rbar S g t := le_Rbar_of Y.K_le Y.K_ne_bot Y.isPGroup_K Y.normal X h7 Y.irr
  have htE : t ∈ Ebar S g K :=
    Y.Abar_le_Ebar hCE X (Subgroup.mem_inf.mpr ⟨X.ht, self_mem_Nbar X.H X.ht⟩)
  have hXR : Xb ≤ Rbar S g t := D.dec.sup ▸ le_sup_left
  obtain ⟨F, -, hFX, -⟩ := D.exists_frame hCE
  obtain ⟨τ, hτY, hτL, hτN⟩ := D.exists_y
  have hτE : τ ∉ Ebar S g K := by
    intro h
    rw [hE] at h
    have h1 : τ ∈ Xb ⊓ Yb := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h).2, hτY⟩
    rw [D.dec.inf, mem_bot] at h1
    exact hτN (h1 ▸ one_mem _)
  obtain ⟨ξ, hξX, hξF⟩ := Y.exists_Xb_not_mem_Fbar X D hE
  have hξR : ξ ∈ Rbar S g t := hXR hξX
  obtain ⟨me, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hξR)
  set a := S.cl (g * S.z * g⁻¹) with ha
  set e := S.cl ((me : G) * g * S.z * ((me : G) * g)⁻¹) with he
  have hea' : ((S.ρ me : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a = e := ρ_cl_conj_z S me X.haQ
  have heF : e ∉ Fbar S g K := hea' ▸ hξF
  have hea : a ≠ e := fun h => heF (h ▸ cl_mem_Fbar Y.H)
  have hte : t ∈ S.Lbar ((me : G) * g) :=
    mem_Lbar_mul_of_commute X.ht (commute_of_mem_Rbar X.haQ hξR)
  have hτe : τ ∈ S.Lbar ((me : G) * g) :=
    mem_Lbar_mul_of_commute hτL (D.dec.comm _ hξX τ hτY)
  have heV : e ∈ Vt S g t := cl_mem_Vt hte
  have hπ : ∀ {r : Rbar S g t}, (r : S.O) ∈ Xb → (F.π r).2 = 1 := by
    intro r hr
    rw [hFX, F.mem_pre] at hr
    obtain ⟨_, h⟩ := hr
    exact mem_Γ₁.mp h
  set rξ : Rbar S g t := ⟨S.ρ me, hξR⟩ with hrξ
  have hrξa : ((resV X.haQ t rξ (aV X.ht) : Vt S g t) : S.Qt) = e := hea'
  have heP : e ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    have hb := (beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ (resV X.haQ t rξ (aV X.ht))).mp (by
      rw [F.beta_eq, F.base, F.φ_resV_aV]
      exact pf_act_Γ₁ _ (hπ hξX))
    rwa [hrξa] at hb
  have hact : act (F.π rξ) E00 ≠ E00 := by
    intro h
    apply hea
    have h1 : F.φ (resV X.haQ t rξ (aV X.ht)) = F.φ (aV X.ht) := by
      rw [F.φ_resV_aV, h, F.base]
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [hrξa] at h2
    exact h2.symm
  obtain ⟨δ, hδ2, hδ⟩ := ((act_Γ₁_add (F.π rξ)).resolve_left (not_not.mpr (hπ hξX))).resolve_left
    hact
  obtain ⟨r', hr'⟩ := F.surj δ
  have hr'X : (r' : S.O) ∈ Xb := by
    rw [hFX, F.mem_pre]
    exact ⟨r'.2, by rw [hr']; exact mem_Γ₁.mpr hδ2⟩
  obtain ⟨ms, hms⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar r'.2)
  have hs : S.cl ((ms : G) * g * S.z * ((ms : G) * g)⁻¹) = a + e := by
    have h1 : F.φ (resV X.haQ t r' (aV X.ht)) =
        F.φ (aV X.ht + resV X.haQ t rξ (aV X.ht)) := by
      rw [F.φ_resV_aV, hr', hδ, map_add, F.base, F.φ_resV_aV]
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [← ρ_cl_conj_z S ms X.haQ, hms]
    rw [Submodule.coe_add, hrξa] at h2
    exact h2
  have hr'R : S.ρ ms ∈ Rbar S g t := hms ▸ r'.2
  have hts : t ∈ S.Lbar ((ms : G) * g) :=
    mem_Lbar_mul_of_commute X.ht (commute_of_mem_Rbar X.haQ hr'R)
  have hτs : τ ∈ S.Lbar ((ms : G) * g) :=
    mem_Lbar_mul_of_commute hτL (D.dec.comm _ (hms ▸ hr'X) τ hτY)
  obtain ⟨x, hxa, hxe, hxV⟩ := Y.exists_x_row hCE X htE hKR hNK hkN hkA hkt heP heV heF hte
  have he0 : e ≠ 0 := pt_ne_zero Y.H me
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S Y.haQ Y.hne
  rcases Y.dich_of_row hCE hτL hτE htE heP hea hs hτe hτs hte hts hxa hxe hxV with
    ⟨m, hτm, hmU⟩ | hτx
  · exact ⟨τ, hτL, hτE, Y.linCase_of hτL hτE hii hτe hea,
      three_le_finrank_of_mem (cl_a_mem_Vt hτL) (cl_mem_Vt hτe) (cl_mem_Vt hτm) ha0 he0 hea
        hmU⟩
  · have hσ : τ * t ∈ S.Lbar g := mul_mem hτL X.ht
    have hσE : τ * t ∉ Ebar S g K := fun h => hτE (by
      have e1 : τ = τ * t * t⁻¹ := by group
      rw [e1]
      exact mul_mem h (inv_mem htE))
    have hσe : τ * t ∈ S.Lbar ((me : G) * g) := mul_mem hτe hte
    refine ⟨τ * t, hσ, hσE, Y.linCase_of hσ hσE hii hσe hea, ?_⟩
    refine three_le_finrank_of_mem (cl_a_mem_Vt hσ) (cl_mem_Vt hσe) (cl_mem_Vt hτx) ha0 he0
      hea fun h => hxV ?_
    exact (Submodule.span_le.mpr (Set.insert_subset (cl_a_mem_Vt X.ht)
      (Set.singleton_subset_iff.mpr heV))) h

end Hyp13

end CFSG.LargeExtraspecial.S13
