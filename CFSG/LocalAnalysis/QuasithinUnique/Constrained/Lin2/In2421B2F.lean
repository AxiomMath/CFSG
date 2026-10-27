module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421B2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

namespace Lin2Hyp0

section F2

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem f_sq_eq_one (hn : n = 2) {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) : f ^ 2 = 1 := by
  obtain ⟨hQL, -, -, hF3, hF4⟩ := complement_facts E.h8 hcfg hB
  obtain ⟨K, _, _, ⟨A⟩⟩ := exists_adapted hcfg.one_pos hcfg.lin2 (E.Rsyl hcfg)
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card hcfg.one_pos A.card_eq
  have hcard : Fintype.card K = 4 := by rw [A.card_eq, hn]; norm_num
  have hfS : f ∈ S := hf.1
  have hOL := E.OL hcfg
  let Hn : Subgroup G := Subgroup.normalizer (L : Set G) ⊓
    Subgroup.normalizer ((blockU L : Subgroup G) : Set G)
  let act : Hn →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)
  have hact : ∀ (g : Hn) (ℓ : L), ((act g ℓ : L) : G) = (g : G) * (ℓ : G) * (g : G)⁻¹ :=
    fun _ _ => rfl
  have hker : ∀ g : Hn, ∀ ℓ : L, A.α (act g ℓ) = 1 ↔ A.α ℓ = 1 := by
    intro g ℓ
    rw [← A.mem_pCoreOf_iff, ← A.mem_pCoreOf_iff, hact, hOL]
    exact (Subgroup.mem_normalizer_iff.1 g.2.2 (ℓ : G)).symm
  obtain ⟨Ψ', hΨ'⟩ := exists_act_quot A.α A.α_surj act hker
  have hmem : ∀ s ∈ S, s ∈ Hn := fun s hs =>
    ⟨hcfg.S_le_normalizer hs, E.S_le_normalizer_U hcfg hs⟩
  set g₁ : Hn := ⟨f, hmem f hfS⟩ with hg₁
  obtain ⟨σ, Gm, hG⟩ := exists_semilinear_of_aut hK2 (Ψ' g₁)
  have hΨ : ∀ Y : SL(2, K), Ψ' g₁ Y = Gm * Matrix.SpecialLinearGroup.map σ.toRingHom Y * Gm⁻¹ :=
    fun Y => eq_mul_inv_iff_mul_eq.2 (hG Y)
  have hσσ : ∀ Y : SL(2, K), Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map σ.toRingHom Y) = Y := by
    intro Y
    apply Subtype.ext
    ext i j
    simp [ringEquiv_apply_apply_of_card_four hcard σ]
  set k : SL(2, K) := Gm * Matrix.SpecialLinearGroup.map σ.toRingHom Gm with hk
  have hf2 : f ^ 2 ∈ S ⊓ Subgroup.normalizer (B : Set G) := pow_mem hf 2
  have hg₂ : (⟨f ^ 2, hmem _ hf2.1⟩ : Hn) = g₁ * g₁ := by
    apply Subtype.ext
    simp [hg₁, pow_two]
  have hfL : ∀ x ∈ L, f ^ 2 * x * (f ^ 2)⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hcfg.S_le_normalizer hf2.1) x).1 hx
  refine hcfg.eq_one_of_inner hQL (hcfg.S_isPGroup.to_le inf_le_left)
    (by rw [inf_comm]; exact hF3) hF4 A hf2 hfL k ?_
  intro ℓ
  have h1 := hΨ' ⟨f ^ 2, hmem _ hf2.1⟩ ℓ
  have h2 : (act ⟨f ^ 2, hmem _ hf2.1⟩ ℓ : L) = ⟨f ^ 2 * ℓ * (f ^ 2)⁻¹, hfL ℓ ℓ.2⟩ := rfl
  rw [h2] at h1
  rw [← h1, hg₂, map_mul, MulAut.mul_apply, hΨ, hΨ]
  simp only [map_mul, map_inv, hσσ, hk, mul_inv_rev]
  group

theorem commutator_T_le_R (hn : n = 2) : ⁅T, T⁆ ≤ thompsonJ S := by
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  obtain ⟨⟨hFcyc, -, hRFS, -, -⟩, -⟩ := E.h12 G T M H S L D n hcfg B hB
  obtain ⟨f, hf⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).1 hFcyc
  have hfF : f ∈ S ⊓ Subgroup.normalizer (B : Set G) := hf ▸ Subgroup.mem_zpowers f
  have hf2 := E.f_sq_eq_one hcfg hn hB hfF
  have hSeq : S = thompsonJ S ⊔ Subgroup.zpowers f := by rw [hf]; exact hRFS.symm
  have hfN : Subgroup.zpowers f ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    Subgroup.zpowers_le.2 (E.TnR hcfg (hcfg.S_le_T hfF.1))
  have h1 : (thompsonJ S).relIndex S ∣ 2 := by
    have := relIndex_sup_of_le_normalizer hfN
    rw [sup_comm, ← hSeq] at this
    rw [this]
    have h2 : Nat.card (Subgroup.zpowers f) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hf2
    exact (Subgroup.index_dvd_card _).trans h2
  have h2 : (thompsonJ S).relIndex T = (thompsonJ S).relIndex S * 2 := by
    rw [← E.idxTS hcfg]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ (thompsonJ_le_self S) hcfg.S_le_T).symm
  refine commutator_le_of_relIndex_dvd_four (E.TnR hcfg) ?_
  rw [h2]
  have := Nat.mul_dvd_mul h1 (dvd_refl 2)
  simpa using this

end F2

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
