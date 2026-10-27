module

public import CFSG.LargeExtraspecial.S10EightH

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

theorem map_eq_of_Lbar_eq_Yb (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k k₁ : S.M}
    (hk₁ : S.ρ k₁ ∈ Yb) (hkk : S.Lbar ((k : G) * g) = S.Lbar ((k₁ : G) * g)) :
    (S.Lbar g ⊓ Xb).map (cK S k) = S.Lbar g ⊓ Xb := by
  rw [D.map_eq_of_Lbar_eq hCE hP hkk]
  exact map_conj_eq_self fun e he => (D.dec.comm e (Subgroup.mem_inf.mp he).2 _ hk₁).symm

end Dec108

section Frame

variable {τ : S.O}

theorem pi_eq_τ₁_of_conj (Y : Hyp10 S g τ) (F : Frame Y) {c₀ e₀ : S.O}
    (hc₀R : c₀ ∈ Rbar S g τ) (hc₀N : c₀ ∉ Nbar S g τ) (hc₀c : c₀ * c₀ = 1)
    (hc₀2 : (F.π ⟨c₀, hc₀R⟩).2 = 1) (he₀ : e₀ ∈ S.Lbar g) (he₀N : e₀ ∉ Nbar S g τ)
    (hπe₀ : F.π ⟨e₀, Lbar_le_Rbar Y.ht he₀⟩ = τ₁) (hce : c₀ * e₀ * c₀⁻¹ ∈ S.Lbar g)
    (hce2 : (F.π ⟨c₀ * e₀ * c₀⁻¹, Lbar_le_Rbar Y.ht hce⟩).2 = 1) :
    F.π ⟨c₀, hc₀R⟩ = τ₁ := by
  have hc₀1 : F.π ⟨c₀, hc₀R⟩ ≠ 1 := fun h => hc₀N ((F.ker _).mp h)
  have hc₀sq : F.π ⟨c₀, hc₀R⟩ * F.π ⟨c₀, hc₀R⟩ = 1 := by
    rw [← map_mul]
    have : (⟨c₀, hc₀R⟩ : Rbar S g τ) * ⟨c₀, hc₀R⟩ = 1 := Subtype.ext hc₀c
    rw [this, map_one]
  have hπce : F.π ⟨c₀ * e₀ * c₀⁻¹, Lbar_le_Rbar Y.ht hce⟩ = τ₁ :=
    eq_τ₁_of_stab_Γ₁ _ (F.π_mem_stabA hce) hce2 (fun h => he₀N (by
      have h1 := conj_mem_Nbar_of_mem_Rbar Y.haQ (inv_mem hc₀R) ((F.ker _).mp h)
      simpa [mul_assoc] using h1))
  have hcomm : F.π ⟨c₀, hc₀R⟩ * τ₁ * (F.π ⟨c₀, hc₀R⟩)⁻¹ = τ₁ := by
    calc F.π ⟨c₀, hc₀R⟩ * τ₁ * (F.π ⟨c₀, hc₀R⟩)⁻¹ =
          F.π ⟨c₀, hc₀R⟩ * F.π ⟨e₀, Lbar_le_Rbar Y.ht he₀⟩ * (F.π ⟨c₀, hc₀R⟩)⁻¹ := by
          rw [hπe₀]
      _ = F.π ⟨c₀ * e₀ * c₀⁻¹, Lbar_le_Rbar Y.ht hce⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
      _ = τ₁ := hπce
  exact eq_τ₁_of_conj _ hc₀2 hc₀sq hc₀1 hcomm

theorem exists_Lbar_eq_of_fix (Y : Hyp10 S g τ) (F : Frame Y) {k' : S.M}
    (hk'R : S.ρ k' ∈ Rbar S g τ) {c₀ : S.O} (hc₀L : c₀ ∈ S.Lbar ((k' : G) * g))
    (hc₀R : c₀ ∈ Rbar S g τ) (hπc₀ : F.π ⟨c₀, hc₀R⟩ = τ₁) {d : S.O} (hdR : d ∈ Rbar S g τ)
    (hσ1 : (F.π ⟨d, hdR⟩).1 = 1) (hσ3 : F.π ⟨d, hdR⟩ ^ 3 = 1) (hσne : F.π ⟨d, hdR⟩ ≠ 1) :
    ∃ k₁ : S.M, (S.ρ k₁ = 1 ∨ S.ρ k₁ = d ∨ S.ρ k₁ = d * d) ∧
      S.Lbar ((k' : G) * g) = S.Lbar ((k₁ : G) * g) := by
  have hfix : ((c₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹))
      = S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) :=
    S.mem_fixLbar.mp (S.cl_mem_fixLbar_self (conj_mem_QG' S k'.2 Y.haQ)) c₀ hc₀L
  set v := resV Y.haQ τ ⟨S.ρ k', hk'R⟩ (aV Y.ht) with hv
  have hvc : (v : S.Qt) = S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) := by
    rw [hv, coe_resV_apply]
    exact ρ_cl_conj_z S k' Y.haQ
  have hact : act τ₁ (act (F.π ⟨S.ρ k', hk'R⟩) E00) = act (F.π ⟨S.ρ k', hk'R⟩) E00 := by
    have e1 : resV Y.haQ τ ⟨c₀, hc₀R⟩ v = v :=
      Subtype.ext (by rw [coe_resV_apply, hvc]; exact hfix)
    have e2 := congrArg F.φ e1
    rw [F.compat, hπc₀, hv, F.φ_resV_aV] at e2
    exact e2
  have hφv : ∀ (r : S.O) (hr : r ∈ Rbar S g τ),
      act (F.π ⟨S.ρ k', hk'R⟩) E00 = act (F.π ⟨r, hr⟩) E00 →
        S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) =
          ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    intro r hr h
    have h1 : v = resV Y.haQ τ ⟨r, hr⟩ (aV Y.ht) := F.φ.injective (by
      rw [hv, F.φ_resV_aV, F.φ_resV_aV]
      exact h)
    rw [← hvc, h1, coe_resV_apply]
    rfl
  obtain ⟨kd, hkd⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hdR)
  rcases fix_τ₁_cases _ _ hact hσ1 hσ3 hσne with h | h | h
  · refine ⟨1, Or.inl (map_one _), ?_⟩
    have h1 := hφv 1 (one_mem _) (by
      rw [h, show (⟨(1 : S.O), one_mem _⟩ : Rbar S g τ) = 1 from rfl, map_one, act_one])
    rw [Subgroup.coe_one, one_mul]
    exact Lbar_eq_of_cl_eq S Y.haQ Y.H.conj_ne (conj_mem_QG' S k'.2 Y.haQ) (by simpa using h1)
  · refine ⟨kd, Or.inr (Or.inl hkd), ?_⟩
    have h1 := hφv d hdR h
    rw [← hkd, ρ_cl_conj_z S kd Y.haQ] at h1
    exact Lbar_eq_of_cl_eq S (conj_mem_QG' S kd.2 Y.haQ) (conj_ne_z' S kd.2 Y.H.conj_ne)
      (conj_mem_QG' S k'.2 Y.haQ) h1
  · refine ⟨kd * kd, Or.inr (Or.inr (by rw [map_mul, hkd])), ?_⟩
    have hddR : d * d ∈ Rbar S g τ := mul_mem hdR hdR
    have h1 := hφv (d * d) hddR (by
      rw [h, ← map_mul]
      rfl)
    rw [← hkd, ← map_mul, ρ_cl_conj_z S (kd * kd) Y.haQ] at h1
    exact Lbar_eq_of_cl_eq S (conj_mem_QG' S (kd * kd).2 Y.haQ)
      (conj_ne_z' S (kd * kd).2 Y.H.conj_ne) (conj_mem_QG' S k'.2 Y.haQ) h1

end Frame

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem exists_Ebar_not_mem_Nbar (hCE : CentralExtInput.{u}) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (Y : Hyp10 S g τ) : ∃ e ∈ S.Lbar g ⊓ Xb, e ∉ Nbar S g τ := by
  by_contra hcon
  push Not at hcon
  have := D.card_LmodN_le_two hCE hτ hcon
  rw [Y.card_LmodN] at this
  omega

theorem exists_map_not_mem_Nbar (hCE : CentralExtInput.{u}) {k : S.M} {τ : S.O}
    (hτk : τ ∈ (S.Lbar g ⊓ Xb).map (cK S k)) (Y : Hyp10 S g τ) :
    ∃ c ∈ (S.Lbar g ⊓ Xb).map (cK S k), c ∉ Nbar S g τ := by
  have hτL := map_le_Lbar_mul (g := g) (Xb := Xb) k hτk
  obtain ⟨k', hk'R, hkk'⟩ := dtEqConj_of_omegaCase Y.H Y.hNo Y.C Y.hΩ k hτL
  by_contra hcon
  push Not at hcon
  have hle : (S.Lbar g ⊓ Xb).map (cK S k) ≤ S.Lbar ((k' : G) * g) ⊓ Nbar S g τ :=
    fun c hc => ⟨hkk' ▸ map_le_Lbar_mul (g := g) (Xb := Xb) k hc, hcon c hc⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_Abar_mul Y hk'R, Subgroup.card_map_of_injective (cK_injective k)] at h1
  have h2 := D.two_mul_card_Ebar hCE
  have h3 := Y.card_Lbar_eq
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g τ : Subgroup S.O) := Nat.card_pos
  omega

theorem eq_of_mem_inf_hyp10 (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k : S.M}
    (hY : ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆)
    (hN : (S.Lbar g ⊓ Xb).map (cK S k) ≤ normalizer ((S.Lbar g ⊓ Xb : Subgroup S.O) : Set S.O))
    {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτk : τ ∈ (S.Lbar g ⊓ Xb).map (cK S k))
    (Y : Hyp10 S g τ) : (S.Lbar g ⊓ Xb).map (cK S k) = S.Lbar g ⊓ Xb := by
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdY := ((D.dec.mem_commutator_iff).mp hdY').1
  have hτL := map_le_Lbar_mul (g := g) (Xb := Xb) k hτk
  obtain ⟨Xτ, Yτ, Dτ, heq⟩ := D.exists_dirDec_of_hyp10 hCE hτ Y
  have hdτ : d ∈ ⁅Yτ, Yτ⁆ := by rw [← heq]; exact hdY'
  obtain ⟨F, hFY, hFX⟩ := Dτ.exists_frame hCE Y
  obtain ⟨hσ1, hσ3, hσne⟩ := Dτ.pi_spec hCE hFY hdτ hd1
  have hπΓ₁ : ∀ x (hx : x ∈ Xτ), (F.π ⟨x, Dτ.le_Rbar_left hx⟩).2 = 1 := fun x hx => by
    have hx' := hx
    rw [hFX] at hx'
    obtain ⟨h, hπ⟩ := (F.mem_pre).mp hx'
    exact mem_Γ₁.mp hπ
  obtain ⟨e₀, he₀, he₀N⟩ := D.exists_Ebar_not_mem_Nbar hCE hτ Y
  have he₀X : e₀ ∈ Xτ := Dτ.mem_Xb_of_mul_self hdτ hd1 (Lbar_le_Rbar hτ.1 he₀.1)
    (S4.mul_self_of_mem_Lbar S X.haQ he₀.1) (D.dec.comm e₀ he₀.2 d hdY)
  have hπe₀ : F.π ⟨e₀, Lbar_le_Rbar Y.ht he₀.1⟩ = τ₁ :=
    eq_τ₁_of_stab_Γ₁ _ (F.π_mem_stabA he₀.1) (hπΓ₁ e₀ he₀X) (fun h => he₀N ((F.ker _).mp h))
  obtain ⟨c₀, hc₀, hc₀N⟩ := D.exists_map_not_mem_Nbar hCE hτk Y
  have hc₀L' := map_le_Lbar_mul (g := g) (Xb := Xb) k hc₀
  have hc₀R : c₀ ∈ Rbar S g τ := Lbar_mul_le_Rbar hτL hc₀L'
  have hc₀c : c₀ * c₀ = 1 := S4.mul_self_of_mem_Lbar S (conj_mem_QG' S k.2 X.haQ) hc₀L'
  have hc₀X : c₀ ∈ Xτ := Dτ.mem_Xb_of_mul_self hdτ hd1 hc₀R hc₀c
    (D.commute_of_map_eq hY hdY' hc₀)
  have hce : c₀ * e₀ * c₀⁻¹ ∈ S.Lbar g ⊓ Xb := (mem_normalizer_iff.mp (hN hc₀) e₀).mp he₀
  have hceX : c₀ * e₀ * c₀⁻¹ ∈ Xτ := mul_mem (mul_mem hc₀X he₀X) (inv_mem hc₀X)
  have hπc₀ := pi_eq_τ₁_of_conj Y F hc₀R hc₀N hc₀c (hπΓ₁ c₀ hc₀X) he₀.1 he₀N hπe₀ hce.1
    (hπΓ₁ _ hceX)
  obtain ⟨k', hk'R, hkk'⟩ := dtEqConj_of_omegaCase Y.H Y.hNo Y.C Y.hΩ k hτL
  obtain ⟨k₁, hk₁, hk'k₁⟩ := exists_Lbar_eq_of_fix Y F hk'R (hkk' ▸ hc₀L') hc₀R hπc₀
    (Dτ.le_Rbar_right ((Dτ.mem_commutator_iff).mp hdτ).1) hσ1 hσ3 hσne
  have hk₁Y : S.ρ k₁ ∈ Yb := by
    rcases hk₁ with h | h | h <;> rw [h]
    · exact one_mem _
    · exact hdY
    · exact mul_mem hdY hdY
  exact D.map_eq_of_Lbar_eq_Yb hCE hP hk₁Y (hkk'.trans hk'k₁)

theorem eq_of_mem_inf (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k : S.M}
    (hN : (S.Lbar g ⊓ Xb).map (cK S k) ≤ normalizer ((S.Lbar g ⊓ Xb : Subgroup S.O) : Set S.O))
    {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1)
    (hτk : τ ∈ (S.Lbar g ⊓ Xb).map (cK S k)) :
    (S.Lbar g ⊓ Xb).map (cK S k) = S.Lbar g ⊓ Xb := by
  have hY := D.map_commutator_eq hCE hP hτ hτ1 hτk
  rcases D.Rbar_eq_or_hyp10 hCE hP hτ hτ1 with ⟨-, hR, -⟩ | Y
  · exact D.eq_of_mem_inf_lin hY hτk hR
  · exact D.eq_of_mem_inf_hyp10 hCE hP hY hN hτ hτk Y

end Dec108

end CFSG.LargeExtraspecial.S10
