module

public import CFSG.LargeExtraspecial.S10EightD
public import CFSG.LargeExtraspecial.S10EightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem Rbar_ne_Lbar (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) :
    Rbar S g τ ≠ S.Lbar g := by
  obtain ⟨k, hkY', hk1, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  have hk3 := ((D.dec.mem_commutator_iff).mp hkY').2
  intro h
  have hkL : S.ρ k ∈ S.Lbar g := h ▸ D.Yb_le_Rbar hτ hkY
  have hkk := S4.mul_self_of_mem_Lbar S X.haQ hkL
  apply hk1
  calc S.ρ k = S.ρ k ^ 3 * (S.ρ k * S.ρ k)⁻¹ := by group
    _ = 1 := by rw [hk3, hkk]; group

theorem Abar_ne_zpowers (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g) : S.Lbar g ⊓ Nbar S g τ ≠ zpowers τ := by
  intro h
  have h1 := card_Lbar_eq_mul X.haQ hτ.1
  rw [D.card_LmodN_eq_four hCE hτ hτ1 hVQ, h, Nat.card_zpowers,
    orderOf_eq_prime (by rw [_root_.sq]; exact S4.mul_self_of_mem_Lbar S X.haQ hτ.1) hτ1] at h1
  have h2 := X.card_Lbar_eq
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := (zpowers_le).mpr X.t_mem_Abar
  apply X.hA
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, X.orderOf_t]
  omega

theorem mem_orbitOf_of_mem_span {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) {k : S.M}
    (hkY : S.ρ k ∈ Yb)
    (hsum : S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
      S.cl (((k * k : S.M) : G) * g * S.z * (((k * k : S.M) : G) * g)⁻¹))
    {w : Vt S g τ} (hw : w ∈ Submodule.span (ZMod 2) {aV hτ.1, bV (D.mem_Lbar_mul hτ hkY)})
    (hw0 : w ≠ 0) : w ∈ orbitOf (RmodN S g τ) (aV hτ.1) := by
  have hkR := D.Yb_le_Rbar hτ hkY
  have hkkY : S.ρ (k * k) ∈ Yb := by rw [map_mul]; exact mul_mem hkY hkY
  have hkkR := D.Yb_le_Rbar hτ hkkY
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hw
  rcases OrthoF2.zmod2_eq_zero_or_eq_one c₁ with rfl | rfl <;>
    rcases OrthoF2.zmod2_eq_zero_or_eq_one c₂ with rfl | rfl
  · exact absurd (by simp) hw0
  · rw [zero_smul, zero_add, one_smul]
    exact ⟨resV X.haQ τ ⟨S.ρ k, hkR⟩, ⟨S.ρ k, hkR, fun v => rfl⟩, D.resV_aV_eq_bV hτ hkY⟩
  · rw [one_smul, zero_smul, add_zero]
    exact ⟨1, one_mem _, rfl⟩
  · rw [one_smul, one_smul]
    refine ⟨resV X.haQ τ ⟨S.ρ (k * k), hkkR⟩, ⟨S.ρ (k * k), hkkR, fun v => rfl⟩,
      Subtype.ext ?_⟩
    change ((S.ρ (k * k) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)
    rw [ρ_cl_conj_z S (k * k) X.haQ]
    exact hsum.symm

theorem Rbar_eq_or_hyp10 (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1) :
    (LinCase S g hτ.1 ∧ Rbar S g τ = (S.Lbar g ⊓ Xb) ⊔ Yb ∧
      finrank (ZMod 2) (Vt S g τ) = 2) ∨ Hyp10 S g τ := by
  have hR := D.Rbar_ne_Lbar hCE hτ
  rcases timmesfeld_4_5 X.H X.hNo X.C hτ.1 hτ1 with hRL | hL | ⟨hVQ, hcase⟩
  · exact absurd hRL hR
  · exact Or.inl ⟨hL, D.Rbar_eq_of_linCase hCE hτ hL, D.finrank_Vt_of_linCase hCE hτ hL⟩
  right
  obtain ⟨k, hkY', -, hne, hPa, hsum⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  have hdim := D.finrank_Vt_of_not_le hCE hτ hτ1 hVQ
  have hcard := D.card_LmodN_eq_four hCE hτ hτ1 hVQ
  have hA := D.Abar_ne_zpowers hCE hτ hτ1 hVQ
  have hf := beta_isAlt X.H X.C hτ.1 hτ1 hVQ
  have hpu : beta X.H X.C hτ.1 hτ1 hVQ (aV hτ.1) (bV (D.mem_Lbar_mul hτ hkY)) = 0 :=
    (beta_aV_eq_zero_iff X.H X.C hτ.1 hτ1 hVQ _).mpr (by rw [coe_bV]; exact hPa)
  have hb0 : bV (D.mem_Lbar_mul hτ hkY) ≠ 0 := fun h => cl_conj_z_ne_zero S
    (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne) (by
      simpa [coe_bV] using congrArg Subtype.val h)
  have hab : aV hτ.1 ≠ bV (D.mem_Lbar_mul hτ hkY) := fun h => hne (by
    have := congrArg Subtype.val h
    rw [coe_bV] at this
    exact this.symm)
  rcases hcase with hSp | hA6 | hΩ | hPGL
  ·
    exfalso
    have h1 := card_spPointRadical hf (beta_nondegenerate X.H X.C hτ.1 hτ1 hVQ)
      (aV_ne_zero X.H hτ.1)
    rw [← hSp.LmodN_eq, hcard, hdim] at h1
    norm_num at h1
  ·
    exfalso
    obtain ⟨x, hx, hxN⟩ : ∃ x ∈ S.Lbar g ⊓ Xb, x ∉ Nbar S g τ := by
      by_contra hcon
      push Not at hcon
      have := D.card_LmodN_le_two hCE hτ hcon
      omega
    have hrx : resV X.haQ τ ⟨x, Lbar_le_Rbar hτ.1 hx.1⟩ ≠ 1 := fun h =>
      hxN ((resV_eq_one_iff X.haQ _).mp h)
    have h1 := (D.resV_Ebar_cases hτ hτ1 hVQ hkY hne hx).resolve_left hrx
    have h2 : spSiegel (beta X.H X.C hτ.1 hτ1 hVQ) hf (aV hτ.1) (bV (D.mem_Lbar_mul hτ hkY)) 0 =
        spRho hf hpu 0 :=
      LinearEquiv.ext fun v => by rw [spSiegel_apply hf hpu, spRho_apply]
    refine hA6.no_typeA _ hpu (fun hmem => ?_) ?_
    · rcases OrthoF2.mem_span_singleton_iff.mp hmem with h | h
      · exact hb0 h
      · exact hab h.symm
    · rw [← h2, ← h1]
      exact ⟨x, hx.1, fun v => rfl⟩
  ·
    refine ⟨X.H, X.hNo, X.C, hτ.1, hτ1, hR, hA, hVQ, hΩ, hdim,
      Submodule.span (ZMod 2) {aV hτ.1, bV (D.mem_Lbar_mul hτ hkY)}, ?_, ?_⟩
    · exact OrthoF2.finrank_span_pair
        (OrthoF2.linearIndependent_pair_iff.mpr ⟨aV_ne_zero X.H hτ.1, hb0, hab⟩)
    · exact fun w hw hw0 => D.mem_orbitOf_of_mem_span hτ hkY hsum hw hw0
  · exact absurd hPGL (hP X.H X.hNo X.C hτ.1 hτ1 hVQ hR hA)

end Dec108

end CFSG.LargeExtraspecial.S10
