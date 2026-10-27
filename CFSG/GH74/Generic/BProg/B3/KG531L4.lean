module

public import CFSG.GH74.Generic.BProg.B3.KG531Defs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.GH74.GLS.IVK

namespace KG531L4

section Algebra

variable {k : Type} [Field k]

theorem commute_of_mulE (ν : kˣ) (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k))
    {M M' : GL (Fin 4) k} {c c' : extension (ν : k)}
    (h : ∀ w : Fin 4 → k, (M : Matrix (Fin 4) (Fin 4) k) *ᵥ w = Ψ (c • Ψ.symm w))
    (h' : ∀ w : Fin 4 → k, (M' : Matrix (Fin 4) (Fin 4) k) *ᵥ w = Ψ (c' • Ψ.symm w)) :
    M * M' = M' * M := by
  refine CFSG.ComponentClassification.OddSelector.eq_of_mulVec_eq fun w => ?_
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, h' w, h w, h, h',
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, smul_smul, smul_smul, mul_comm]

end Algebra

section Row

variable {A : Type} [Group A] {K : Subgroup A} {k : Type} [Field k] [Finite k]
  {ρ : A →* MulAut (projectiveSL 4 k)}

theorem exists_mulE (ν : kˣ) (hν : ¬ IsSquare (ν : k))
    (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k)) (C : GL (Fin 4) k)
    (h9 : K.map ρ = (rowSJ ν Ψ).map (MulAut.conj (conjAut 4 k C)).toMonoidHom)
    {b : A} (hbK : b ∈ centralizer (K : Set A)) {Bb : GL (Fin 4) k}
    (hρb : ρ b = conjAut 4 k Bb) :
    ∃ c : extension (ν : k), ∀ w : Fin 4 → k,
      ((C⁻¹ * Bb * C : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ w = Ψ (c • Ψ.symm w) := by
  have hcent : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)),
      conjAut 4 k Bb * conjAut 4 k (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) =
        conjAut 4 k (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) * conjAut 4 k Bb := by
    intro g
    have hmem : (MulAut.conj (conjAut 4 k C))
        (conjAut 4 k (rowSPi ν Ψ (SpecialLinearGroup.toGL g))) ∈ K.map ρ := by
      rw [h9]
      exact ⟨conjAut 4 k (rowSPi ν Ψ (SpecialLinearGroup.toGL g)), ⟨g, rfl⟩, rfl⟩
    obtain ⟨x, hxK, hx⟩ := hmem
    have h1 : x * b = b * x := Subgroup.mem_centralizer_iff.1 hbK x hxK
    have h2' : ρ x * ρ b = ρ b * ρ x := by rw [← map_mul, ← map_mul, h1]
    rw [hx, hρb] at h2'
    simp only [MulAut.conj_apply, map_mul, map_inv] at h2' ⊢
    exact h2'.symm
  have hsc : ∀ (c : kˣ) (Y Z : GL (Fin 4) k),
      Y * (GeneralLinearGroup.scalar (Fin 4) c * Z) =
        GeneralLinearGroup.scalar (Fin 4) c * (Y * Z) := fun c Y Z => by
    rw [← mul_assoc, ← scalar_comm' c Y, mul_assoc]
  have hlin : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
      (C⁻¹ * Bb * C) * rowSPi ν Ψ (SpecialLinearGroup.toGL g) =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) *
          (C⁻¹ * Bb * C) := by
    intro g
    obtain ⟨c, hc'⟩ := exists_scalar_of_conjAut_comm (by norm_num) Bb
      (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) (hcent g)
    refine ⟨c, ?_⟩
    calc (C⁻¹ * Bb * C) * rowSPi ν Ψ (SpecialLinearGroup.toGL g)
        = C⁻¹ * (Bb * (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹)) * C := by group
      _ = C⁻¹ * (GeneralLinearGroup.scalar (Fin 4) c *
            (C * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * C⁻¹) * Bb) * C := by rw [hc']
      _ = GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) *
            (C⁻¹ * Bb * C) := by
          rw [mul_assoc (GeneralLinearGroup.scalar (Fin 4) c), hsc]
          group
  have : Nontrivial (extension (ν : k)) := (extension_isField (ν : k) hν).nontrivial
  exact RowSComm.exists_mul_of_normalizes ν Ψ (C⁻¹ * Bb * C) hlin

theorem commute_of_rowS (ν : kˣ) (hν : ¬ IsSquare (ν : k))
    (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k)) (C : GL (Fin 4) k)
    (hinj : Function.Injective ρ)
    (h9 : K.map ρ = (rowSJ ν Ψ).map (MulAut.conj (conjAut 4 k C)).toMonoidHom)
    {b₁ b₂ : A} (hb₁ : b₁ ∈ centralizer (K : Set A)) (hb₂ : b₂ ∈ centralizer (K : Set A))
    {B₁ B₂ : GL (Fin 4) k} (h₁ : ρ b₁ = conjAut 4 k B₁) (h₂ : ρ b₂ = conjAut 4 k B₂) :
    b₁ * b₂ = b₂ * b₁ := by
  obtain ⟨c₁, hc₁⟩ := exists_mulE ν hν Ψ C h9 hb₁ h₁
  obtain ⟨c₂, hc₂⟩ := exists_mulE ν hν Ψ C h9 hb₂ h₂
  have hM := commute_of_mulE ν Ψ hc₁ hc₂
  have hB : B₁ * B₂ = B₂ * B₁ := by
    have h : C⁻¹ * (B₁ * B₂) * C = C⁻¹ * (B₂ * B₁) * C :=
      calc C⁻¹ * (B₁ * B₂) * C = (C⁻¹ * B₁ * C) * (C⁻¹ * B₂ * C) := by group
        _ = (C⁻¹ * B₂ * C) * (C⁻¹ * B₁ * C) := hM
        _ = C⁻¹ * (B₂ * B₁) * C := by group
    exact mul_left_cancel (mul_right_cancel h)
  apply hinj
  rw [map_mul, map_mul, h₁, h₂, ← map_mul, ← map_mul, hB]

end Row

end KG531L4

theorem kg531_l4 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (_hmod : p ^ f % 8 ≠ 1) :
    KG531Empty (fun X _ => LieModel X .PSL 4 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  classical
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.S45.LQ.stated_of_lieModel_PSL hL
  let φ : S ≃* projectiveSL 4 F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F))
  have hZ := center_projectiveSL_eq_bot (k := F) (show 3 ≤ 4 by norm_num)
  have hCW : centralizer (((⊤ : Subgroup S) : Subgroup S) : Set S) = ⊥ := by
    rw [← CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab]
    ext g
    simp only [Subgroup.mem_centralizer_iff, Subgroup.coe_top, Set.mem_univ, forall_const,
      Subgroup.mem_center_iff]
  let φ' : (⊤ : Subgroup S) ≃* projectiveSL 4 F := Subgroup.topEquiv.trans φ
  obtain ⟨ρ, hinj, hρW, -, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_extension (W := ⊤) hCW φ' hZ
  have hK : CFSG.Assembly.IsComponentOf B₁ (centralizer ({t} : Set S)) :=
    (isComponentOf_iff_isComponent_subgroupOf h.comp₁.1).2 h.comp₁.2
  obtain ⟨hW, hCA, hCW', hL₁⟩ :=
    CFSG.ComponentClassification.OddSelector.socle_images φ' hinj hρW le_top hK
  have hinner : ∀ b : S, ∃ B : GL (Fin 4) F, ρ b = conjAut 4 F B := fun b => by
    have hb : ρ b ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 4 F) :=
      hW ▸ ⟨b, Subgroup.mem_top b, rfl⟩
    obtain ⟨B, hB⟩ := inner_le_range_conjAut hb
    exact ⟨B, hB.symm⟩
  have hodd : Odd (Nat.card (center ↥B₁)) := by
    rw [h.center₁, Subgroup.card_bot]
    exact odd_one
  rcases l4_type hp hp2 hf hF h.odd (Or.inl h.model₁) hodd hinj h.t_ord hL₁ with
    ⟨B, μ, hρt, hμ, hsq⟩ | ⟨B, hρt, -⟩
  ·
    have : CharP F p := finite_field_prime_power_characteristic hp hf hF
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
    obtain ⟨hS, -⟩ := selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρt hμ hsq
    obtain ⟨ν, hν, Ψ, C, -, -, -, -, -, -, -, -, h9, -, -, -, -, -⟩ := hS
    have hcomm : ∀ b₁ ∈ B₂, ∀ b₂ ∈ B₂, b₁ * b₂ = b₂ * b₁ := by
      intro b₁ hb₁ b₂ hb₂
      obtain ⟨Bb₁, h₁⟩ := hinner b₁
      obtain ⟨Bb₂, h₂⟩ := hinner b₂
      exact KG531L4.commute_of_rowS ν hν Ψ C hinj h9
        (Subgroup.mem_centralizer_iff.2 fun x hx => h.comm x hx b₁ hb₁)
        (Subgroup.mem_centralizer_iff.2 fun x hx => h.comm x hx b₂ hb₂) h₁ h₂
    obtain ⟨a, b, hab⟩ := h.comp₂.2.1.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hxy : x * y = y * x :=
      Subtype.ext (Subtype.ext (hcomm (x.1 : S) x.2 (y.1 : S) y.2))
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy])
  ·
    obtain ⟨B₀, hB₀⟩ := hinner t
    have h2 : dualAut 4 F = conjAut 4 F (B⁻¹ * B₀) := by
      rw [map_mul, map_inv]
      calc dualAut 4 F = (conjAut 4 F B)⁻¹ * (conjAut 4 F B * dualAut 4 F) := by group
        _ = (conjAut 4 F B)⁻¹ * conjAut 4 F B₀ := by rw [← hρt, hB₀]
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F) (n := 4) (by norm_num)
    rw [h2]
    exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

end CFSG.GH74.Generic.BProg.B3
