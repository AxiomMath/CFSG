module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeMatrix
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviMain
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeTorus

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock longInv shortBlock)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open CFSG.ClassicalInvolution.RouteD.NodeModel
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups commutatorElement

section Act

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

@[expose] def DiagAct (ψ : StatedSp 2 (GaloisField p f) →* G) (c : G) : Prop :=
  ∃ A : gsp 2 (GaloisField p f), ((A : GL (Fin 2 ⊕ Fin 2) (GaloisField p f)) :
    Mat4 (GaloisField p f)).IsDiag ∧ ∀ x, c * ψ x * c⁻¹ = ψ (conjSp 2 (GaloisField p f) A x)

omit [Finite G] in
theorem exists_lift_of_normalizes (S : CSetupW p f 2 Ω K z)
    {ψ : StatedSp 2 (GaloisField p f) →* G} (hψ : Function.Injective ψ) {c : G}
    (hc : conjSub c ψ.range = ψ.range) :
    ∃ (A : gsp 2 (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f), ∀ x,
      c * ψ x * c⁻¹ = ψ (conjSp 2 (GaloisField p f) A (fieldSp 2 (GaloisField p f) σ x)) := by
  have hodd : ringChar (GaloisField p f) ≠ 2 := ringChar_ne_two_of_two_ne_zero' S.two_ne_zero
  have hker : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f)) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  have hmem : ∀ x, c * ψ x * c⁻¹ ∈ ψ.range := fun x => by
    have := conj_mem_conjSub (n := c) (K := ψ.range) (x := ψ x) ⟨x, rfl⟩
    rwa [hc] at this
  have hmem' : ∀ x, c⁻¹ * ψ x * c ∈ ψ.range := fun x => by
    have : ψ x ∈ conjSub c ψ.range := by
      rw [hc]
      exact ⟨x, rfl⟩
    exact mem_conjSub_iff.mp this
  obtain ⟨A, σ, hA⟩ := exists_semilinear_lift' hodd S.four_le ψ hker (MulAut.conj c)
    (fun x => by simpa [MulAut.conj_apply] using hmem x)
    (fun x => by simpa [MulAut.conj_symm_apply] using hmem' x)
  exact ⟨A, σ, fun x => by simpa [MulAut.conj_apply] using hA x⟩

omit [Finite G] in
theorem DiagAct.commutator_commute {ψ : StatedSp 2 (GaloisField p f) →* G} {c₁ c₂ : G}
    (h₁ : DiagAct ψ c₁) (h₂ : DiagAct ψ c₂) (x : StatedSp 2 (GaloisField p f)) :
    ⁅c₁, c₂⁆ * ψ x = ψ x * ⁅c₁, c₂⁆ := by
  obtain ⟨A₁, hd₁, hA₁⟩ := h₁
  obtain ⟨A₂, hd₂, hA₂⟩ := h₂
  have inv_act : ∀ {c : G} {A : gsp 2 (GaloisField p f)},
      (∀ x, c * ψ x * c⁻¹ = ψ (conjSp 2 (GaloisField p f) A x)) →
      ∀ x, c⁻¹ * ψ x * c = ψ (conjSp 2 (GaloisField p f) A⁻¹ x) := by
    intro c A h x
    have h1 : conjSp 2 (GaloisField p f) A (conjSp 2 (GaloisField p f) A⁻¹ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have h' := h (conjSp 2 (GaloisField p f) A⁻¹ x)
    rw [h1] at h'
    calc c⁻¹ * ψ x * c = c⁻¹ * (c * ψ (conjSp 2 (GaloisField p f) A⁻¹ x) * c⁻¹) * c := by
          rw [h']
      _ = ψ (conjSp 2 (GaloisField p f) A⁻¹ x) := by group
  have e1 := inv_act hA₂ x
  have e2 := inv_act hA₁ (conjSp 2 (GaloisField p f) A₂⁻¹ x)
  have e3 := hA₂ (conjSp 2 (GaloisField p f) A₁⁻¹ (conjSp 2 (GaloisField p f) A₂⁻¹ x))
  have e4 := hA₁ (conjSp 2 (GaloisField p f) A₂
    (conjSp 2 (GaloisField p f) A₁⁻¹ (conjSp 2 (GaloisField p f) A₂⁻¹ x)))
  have key : ⁅c₁, c₂⁆ * ψ x * ⁅c₁, c₂⁆⁻¹ = ψ x := by
    calc ⁅c₁, c₂⁆ * ψ x * ⁅c₁, c₂⁆⁻¹
        = c₁ * (c₂ * (c₁⁻¹ * (c₂⁻¹ * ψ x * c₂) * c₁) * c₂⁻¹) * c₁⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ψ (conjSp 2 (GaloisField p f) A₁ (conjSp 2 (GaloisField p f) A₂
            (conjSp 2 (GaloisField p f) A₁⁻¹ (conjSp 2 (GaloisField p f) A₂⁻¹ x)))) := by
          rw [e1, e2, e3, e4]
      _ = ψ x := by rw [conjSp_commutator_of_isDiag hd₁ hd₂]
  exact mul_inv_eq_iff_eq_mul.mp key

end Act

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z}
  (P : LeviParams S Fr)

namespace LeviParams

theorem act_dichotomy (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) {c : G}
    (hcT : ∀ t ∈ P.T₀, t * c = c * t) :
    (DiagAct P.ψ₂ c ∧ c * Fr.zf 0 * c⁻¹ = Fr.zf 0) ∨ c * Fr.zf 0 * c⁻¹ = Fr.zf 1 := by
  have hc2 : c * Fr.zf 2 = Fr.zf 2 * c := (hcT _ (P.zf_two_mem hconn hZ)).symm
  have hnorm : conjSub c (Mf Fr 0 1) = Mf Fr 0 1 :=
    conjSub_Mf_eq_of_commute S Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide) hc2
  obtain ⟨A, σ, hA⟩ := exists_lift_of_normalizes S P.ψ₂_injective
    (by rw [P.ψ₂_range]; exact hnorm)
  have hfix : ∀ B : SL(2, GaloisField p f),
      conjSp 2 (GaloisField p f) A (fieldSp 2 (GaloisField p f) σ
        (shortBlock (GaloisField p f) fin_two_zero_ne_one B)) =
        shortBlock (GaloisField p f) fin_two_zero_ne_one B := by
    intro B
    apply P.ψ₂_injective
    rw [← hA]
    have hmem : P.ψ₂ (shortBlock (GaloisField p f) fin_two_zero_ne_one B) ∈ P.T₀ := by
      rw [P.T₀_eq]
      exact Subgroup.mem_map_of_mem _ ⟨B, rfl⟩
    exact mul_inv_eq_iff_eq_mul.mpr (hcT _ hmem).symm
  obtain ⟨hσ, hcase⟩ := fix_shortBlock_dichotomy S.two_ne_zero A σ hfix
  subst hσ
  have e0 : P.ψ₂ (longInv (GaloisField p f) 2 0) = Fr.zf 0 := P.ψ₂_longInv 0
  have e1 : P.ψ₂ (longInv (GaloisField p f) 2 1) = Fr.zf 1 := P.ψ₂_longInv 1
  have hz : c * Fr.zf 0 * c⁻¹ =
      P.ψ₂ (conjSp 2 (GaloisField p f) A (longInv (GaloisField p f) 2 0)) := by
    rw [← e0, hA]
    simp
  rcases hcase with ⟨hd, hfixz⟩ | hswap
  · refine Or.inl ⟨⟨A, hd, fun x => by rw [hA]; simp⟩, ?_⟩
    rw [hz, hfixz, e0]
  · refine Or.inr ?_
    rw [hz, hswap, e1]

theorem diagAct_of_centralizes_layer {c : G} (hcM : ∀ m ∈ Mf Fr 0 1, m * c = c * m)
    (hcx : P.x₂ * c = c * P.x₂) : DiagAct P.ψ₀ c := by
  have hc0 : c * Fr.zf 0 = Fr.zf 0 * c :=
    (hcM _ (Kf_le_Mf Fr 0 (Or.inl rfl) (Frame.zf_memW S 0))).symm
  have hnorm : conjSub c (Mf Fr 1 2) = Mf Fr 1 2 :=
    conjSub_Mf_eq_of_commute S Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide)
      (by decide) hc0
  obtain ⟨A, σ, hA⟩ := exists_lift_of_normalizes S P.ψ₀_injective
    (by rw [P.ψ₀_range]; exact hnorm)
  have hK₁ : ∀ B : SL(2, GaloisField p f),
      P.ψ₀ (longBlock (GaloisField p f) 2 0 B) ∈ Mf Fr 0 1 := by
    intro B
    have h : P.ψ₀ (longBlock (GaloisField p f) 2 0 B) ∈
        (longBlock (GaloisField p f) 2 0).range.map P.ψ₀ :=
      Subgroup.mem_map_of_mem _ ⟨B, rfl⟩
    rw [LeviParams.ψ₀, P.LF₀.map_layerSp_longBlock S 0] at h
    exact Kf_le_Mf Fr 1 (Or.inr rfl) h
  have hfix0 : ∀ B : SL(2, GaloisField p f),
      conjSp 2 (GaloisField p f) A (fieldSp 2 (GaloisField p f) σ
        (longBlock (GaloisField p f) 2 0 B)) = longBlock (GaloisField p f) 2 0 B := by
    intro B
    apply P.ψ₀_injective
    rw [← hA]
    exact mul_inv_eq_iff_eq_mul.mpr (hcM _ (hK₁ B)).symm
  have hfixT : conjSp 2 (GaloisField p f) A (fieldSp 2 (GaloisField p f) σ
      (longBlock (GaloisField p f) 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom
        (GaloisField p f) P.b))) =
      longBlock (GaloisField p f) 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom
        (GaloisField p f) P.b) := by
    apply P.ψ₀_injective
    rw [← hA]
    exact mul_inv_eq_iff_eq_mul.mpr hcx.symm
  obtain ⟨hσ, hd⟩ := diag_of_fix_long_torus A σ hfix0 P.b P.hb hfixT
  subst hσ
  exact ⟨A, hd, fun x => by rw [hA]; simp⟩

end LeviParams

end Levi

end CFSG.ClassicalInvolution.RouteD
