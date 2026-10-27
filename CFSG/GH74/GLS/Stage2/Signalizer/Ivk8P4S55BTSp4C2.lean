module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4C
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4F
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4P2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {F : Type} [Field F] [Finite F] {W I Q : Subgroup (StatedProj (StatedSp 2 F))}
  {N : Submodule F (Fin 2 ⊕ Fin 2 → F)} {g : StatedSp 2 F}

theorem false_of_flag_one (h2 : (2 : F) ≠ 0) (hI : ⁅I, I⁆ = I)
    (hIW : I ≤ normalizer (W : Set (StatedProj (StatedSp 2 F)))) (hQI : Q ≤ I)
    (hQ : IVK.IsFourSubgroup Q)
    (hN : ∀ A : GL (Fin 2 ⊕ Fin 2) F,
      A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set (GL (Fin 2 ⊕ Fin 2) F)) →
        ∀ v ∈ N, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N)
    (hg : (flag 2 F 1).map (spAct g) = N) : False := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab1, haa, hbb, habab⟩ := exists_pair_four hQ
  have hD : ⁅conjPre I g, conjPre I g⁆.map (proj 2 F) =
      I.map (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom := by
    rw [Subgroup.map_commutator, map_conjPre, OFC.perfect_map hI]
  have hmem : ∀ y ∈ Q, (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom y ∈
      ⁅conjPre I g, conjPre I g⁆.map (proj 2 F) := fun y hy => by
    rw [hD]
    exact ⟨y, hQI hy, rfl⟩
  obtain ⟨x₁, hx₁, h₁⟩ := hmem a ha
  obtain ⟨x₂, hx₂, h₂⟩ := hmem b hb
  have hsc : ∀ x : StatedSp 2 F, x ∈ spScalars 2 F ↔ proj 2 F x = 1 := fun x => by
    rw [← ker_proj, MonoidHom.mem_ker]
  have hc1 : ∀ y, (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom y = 1 → y = 1 := fun y hy =>
    (MulAut.conj (proj 2 F g)⁻¹).injective (hy.trans (map_one _).symm)
  refine false_of_point h2 (fun x hx => exists_mulVec_e0 (conjPre_flag hIW hN hg hx)) hx₁ hx₂
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsc, map_mul, h₁, ← map_mul, haa, map_one]
  · rw [hsc, map_mul, h₂, ← map_mul, hbb, map_one]
  · rw [hsc, map_mul, map_mul, h₁, h₂, ← map_mul, ← map_mul, habab, map_one]
  · rw [hsc, h₁]
    exact fun h => ha1 (hc1 a h)
  · rw [hsc, h₂]
    exact fun h => hb1 (hc1 b h)
  · rw [hsc, map_mul, h₁, h₂, ← map_mul]
    exact fun h => hab1 (hc1 _ h)

theorem false_of_flag_two {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (h2 : (2 : F) ≠ 0)
    {U : Subgroup (MulAut (StatedProj (StatedSp 2 F)))} (hI : ⁅I, I⁆ = I)
    (hIW : I ≤ normalizer (W : Set (StatedProj (StatedSp 2 F)))) (hQI : Q ≤ I)
    (hQ : IVK.IsFourSubgroup Q) (hU : IVK.IsFourSubgroup U) (hUW : ∀ u ∈ U, ∀ w ∈ W, u w ∈ W)
    (hUI : ∀ u ∈ U, ∀ x ∈ I, u x = x) (hadm : ∀ u ∈ U, u ≠ 1 → AdmAut k u)
    (hN : ∀ A : GL (Fin 2 ⊕ Fin 2) F,
      A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set (GL (Fin 2 ⊕ Fin 2) F)) →
        ∀ v ∈ N, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N)
    (hg : (flag 2 F 2).map (spAct g) = N) : False := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu₁₂, hsq₁, hsq₂, hsq₁₂⟩ := exists_pair_four hU
  obtain ⟨A₁, rfl⟩ := linear_of_admAut hk hp hp2 hf hcard hsq₁ hu₁1 (hadm _ hu₁ hu₁1)
  obtain ⟨A₂, rfl⟩ := linear_of_admAut hk hp hp2 hf hcard hsq₂ hu₂1 (hadm _ hu₂ hu₂1)
  have hfl : ∀ A : gsp 2 F, conjAut 2 F A ∈ U →
      ((conjB g (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 := fun A hA =>
    toBlocks₂₁_eq_zero_of_flag (mulVec_mem_flag_of_conj hg
      (hN _ (mem_normalizer_preGL_of_conjAut (hUW _ hA))) (by simp only [conjB]; group))
  have hcen : ∀ A : gsp 2 F, conjAut 2 F A ∈ U → ∀ x ∈ conjPre I g,
      ∃ s ∈ center (GL (Fin 2 ⊕ Fin 2) F), conjB g (A : GL (Fin 2 ⊕ Fin 2) F) *
        ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * (conjB g (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ =
          s * x := by
    intro A hA x hx
    obtain ⟨s, hs, hse⟩ := exists_central_of_conjAut (hUI _ hA _ (proj_conj_mem hx))
    exact ⟨s, hs, conjB_central hs hse⟩
  obtain ⟨μ₁, hJ₁⟩ := conjB_gsp (g := g) A₁
  obtain ⟨μ₂, hJ₂⟩ := conjB_gsp (g := g) A₂
  obtain ⟨l₁, hl₁⟩ := sq_smul_of_conjAut hsq₁
  obtain ⟨l₂, hl₂⟩ := sq_smul_of_conjAut hsq₂
  obtain ⟨l₁₂, hl₁₂⟩ := sq_smul_of_conjAut (A := A₁ * A₂) (by rw [map_mul]; exact hsq₁₂)
  have hns₁₂ := ne_smul_of_conjAut (A := A₁ * A₂) (by rw [map_mul]; exact hu₁₂)
  rw [Subgroup.coe_mul] at hl₁₂ hns₁₂
  have hIne : I.map (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective] at h
    have h4 := hQ.2
    rw [le_bot_iff.mp (hQI.trans h.le), Subgroup.card_bot] at h4
    norm_num at h4
  refine false_of_lagrangian h2 (I := conjPre I g)
    (fun x hx => toBlocks₂₁_eq_zero_of_flag (conjPre_flag hIW hN hg hx))
    (by rw [map_conjPre]; exact OFC.perfect_map hI _) (by rw [map_conjPre]; exact hIne)
    hJ₁ hJ₂ (hfl A₁ hu₁) (hfl A₂ hu₂) ⟨l₁, conjB_sq hl₁⟩ ⟨l₂, conjB_sq hl₂⟩
    ⟨l₁₂, by rw [conjB_mul]; exact conjB_sq hl₁₂⟩
    (conjB_ne (ne_smul_of_conjAut hu₁1)) (conjB_ne (ne_smul_of_conjAut hu₂1))
    (by rw [conjB_mul]; exact conjB_ne hns₁₂) (hcen A₁ hu₁) (hcen A₂ hu₂)

theorem not_btConfig_psp4 {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) :
    ¬ BTConfig k p (StatedProj (StatedSp 2 F)) := by
  rintro ⟨W, I, Q, U, hW, hWp, hI, hIW, hQI, hQ, hU, hUW, hUI, hadm⟩
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_psp4 hp hp2 hcard)
  obtain ⟨N, hN0, hNiso, hN⟩ := exists_isotropic_subspace hp2 hW hWp
  obtain ⟨d, g, hd1, hd2, hg⟩ := exists_map_flag_eq_of_isTotallyIsotropic hN0 hNiso
  interval_cases d
  · exact false_of_flag_one h2 hI hIW hQI hQ hN hg
  · exact false_of_flag_two hk hp hp2 hf hcard h2 hI hIW hQI hQ hU hUW hUI hadm hN hg

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
