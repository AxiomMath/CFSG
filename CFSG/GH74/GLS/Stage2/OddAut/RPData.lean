module

public import CFSG.GH74.GLS.Stage2.OddAut.RPCore
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRadicalRigidity

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.Bender.Thm1

section Data

variable {C : Type} [Group C] {p : ℕ}

variable (C p) in
@[expose] def PCharData (A : Subgroup (MulAut C)) : Prop :=
  ∀ S : Sylow p C, ∀ P : Subgroup C, Subgroup.normalizer ((S : Subgroup C) : Set C) ≤ P → P ≠ ⊤ →
    ∃ Q : Subgroup C, Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ IsPGroup p Q ∧
      ∀ α ∈ A, (∀ q ∈ Q, α q = q) → α ∈ Q.map (MulAut.conj : C →* MulAut C)

theorem conj_conj_mul (c x : C) : MulAut.conj c * MulAut.conj x * (MulAut.conj c)⁻¹ =
    MulAut.conj (c * x * c⁻¹) := by
  simp only [← map_mul, ← map_inv]

omit [Group C] in
theorem normal_subgroupOf_map {G H : Type*} [Group G] [Group H] (f : G ≃* H) {Q P : Subgroup G}
    (hQP : Q ≤ P) (h : (Q.subgroupOf P).Normal) :
    ((Q.map f.toMonoidHom).subgroupOf (P.map f.toMonoidHom)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨g', hg', hgg⟩ := g.2
  have h1 : (⟨g', hg'⟩ : ↥P) * (⟨q, hQP hq⟩ : ↥P) * (⟨g', hg'⟩ : ↥P)⁻¹ ∈ Q.subgroupOf P :=
    h.conj_mem _ (Subgroup.mem_subgroupOf.2 hq) _
  have h2 : g' * q * g'⁻¹ ∈ Q := Subgroup.mem_subgroupOf.1 h1
  refine Subgroup.mem_subgroupOf.2 ⟨g' * q * g'⁻¹, h2, ?_⟩
  have e1 : f q = (x : H) := hqx
  have e2 : f g' = (g : H) := hgg
  show f (g' * q * g'⁻¹) = (g : H) * (x : H) * (g : H)⁻¹
  rw [map_mul, map_mul, map_inv, e1, e2]

theorem PCharData.of_standard [Finite C] [Fact p.Prime] {A : Subgroup (MulAut C)}
    (hInnA : (MulAut.conj : C →* MulAut C).range ≤ A) (U : Sylow p C)
    (h : ∀ P : Subgroup C, Subgroup.normalizer ((U : Subgroup C) : Set C) ≤ P → P ≠ ⊤ →
      ∃ Q : Subgroup C, Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ IsPGroup p Q ∧
        ∀ α ∈ A, (∀ q ∈ Q, α q = q) → α ∈ Q.map (MulAut.conj : C →* MulAut C)) :
    PCharData C p A := by
  intro S P hSP hP
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C U S
  have hcoe : (S : Subgroup C) = (U : Subgroup C).map (MulAut.conj c).toMonoidHom := by
    subst hc
    exact Sylow.coe_subgroup_smul (g := c) (P := U)
  have hcc : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom = MonoidHom.id C := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  set P' : Subgroup C := P.map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hPeq : P = P'.map (MulAut.conj c).toMonoidHom := by
    rw [hP', Subgroup.map_map, hcc, Subgroup.map_id]
  have hUP' : Subgroup.normalizer ((U : Subgroup C) : Set C) ≤ P' := by
    intro x hx
    have h1 : (MulAut.conj c) x ∈ Subgroup.normalizer ((S : Subgroup C) : Set C) := by
      rw [hcoe, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨x, hx, rfl⟩
    refine ⟨(MulAut.conj c) x, hSP h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP'top : P' ≠ ⊤ := by
    intro htop
    apply hP
    rw [hPeq, htop]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective
  obtain ⟨Q', hQ'P', hQ'n, hQ'p, hQ'r⟩ := h P' hUP' hP'top
  refine ⟨Q'.map (MulAut.conj c).toMonoidHom, ?_, ?_, hQ'p.map _, ?_⟩
  · rw [hPeq]
    exact Subgroup.map_mono hQ'P'
  · rw [hPeq]
    exact normal_subgroupOf_map (MulAut.conj c) hQ'P' hQ'n
  · intro α hαA hα
    have hconjmem : ∀ x : C, MulAut.conj x ∈ A := fun x => hInnA ⟨x, rfl⟩
    obtain ⟨q, hq, hqα⟩ := hQ'r ((MulAut.conj c)⁻¹ * α * MulAut.conj c)
      (A.mul_mem (A.mul_mem (A.inv_mem (hconjmem c)) hαA) (hconjmem c)) (by
      intro q hq
      have hmem : (MulAut.conj c) q ∈ Q'.map (MulAut.conj c).toMonoidHom := ⟨q, hq, rfl⟩
      have h1 := hα _ hmem
      show (MulAut.conj c)⁻¹ (α ((MulAut.conj c) q)) = q
      rw [h1]
      simp only [MulAut.inv_apply_self])
    refine ⟨c * q * c⁻¹, ⟨q, hq, rfl⟩, ?_⟩
    have h2 : α = MulAut.conj c * ((MulAut.conj c)⁻¹ * α * MulAut.conj c) *
        (MulAut.conj c)⁻¹ := by
      simp [mul_assoc]
    rw [h2, ← hqα]
    exact (conj_conj_mul c q).symm

theorem parCharP_of_data [Finite C] [Fact p.Prime] {A : Subgroup (MulAut C)}
    (hcen : Subgroup.center C = ⊥) (hd : PCharData C p A) : ParCharP C p A := by
  intro R hRne hRp hcore hNne hSyl G hGA hconjG hstab
  obtain ⟨S, hS⟩ := hSyl
  obtain ⟨Q, hQP, hQn, hQp, hQr⟩ := hd S (Subgroup.normalizer (R : Set C)) hS hNne
  have hQR : Q ≤ R := by
    rw [← hcore]
    exact le_pCoreOf p hQP hQn hQp
  have hCA : ∀ α ∈ A, (∀ u ∈ R, α u = u) →
      α ∈ R.map (MulAut.conj : C →* MulAut C) := by
    intro α hαA hα
    obtain ⟨q, hq, hqα⟩ := hQr α hαA (fun q hq => hα q (hQR hq))
    exact ⟨q, hQR hq, hqα⟩
  have hRA : R.map (MulAut.conj : C →* MulAut C) ≤ A := by
    rintro _ ⟨r, hr, rfl⟩
    exact hGA (hconjG ⟨r, hr, rfl⟩)
  exact (CFSG.LocalAnalysis.ComponentInitial.automorphism_normalizer_from_pointwise_radical_rigidity
    hcen hRp hRA hCA hconjG (fun α hα => ⟨hGA hα, hstab α hα⟩)).1

theorem false_of_rp_data [Finite C] [Fact p.Prime] {A : Subgroup (MulAut C)} (hBT : Holds C p)
    (hcen : Subgroup.center C = ⊥) (hd : PCharData C p A)
    (hInnA : (MulAut.conj : C →* MulAut C).range ≤ A) {V Z : Subgroup (MulAut C)} (hVA : V ≤ A)
    (hZA : Z ≤ A) (h2 : N2Cfg C p V Z) (h3 : N3Full C V Z)
    (hin : ∃ v ∈ V, v ≠ 1 ∧ v ∈ (MulAut.conj : C →* MulAut C).range) : False :=
  false_of_rp hBT hcen (parCharP_of_data hcen hd) hInnA hVA hZA h2 h3 hin

end Data

end CFSG.GH74.GLS.Stage2.OddAut
