module

public import Certificates.Certificate16982
public import Certificates.Certificate16963
public import Certificates.Certificate16964

public section

namespace CFSG.GF2Type.Smith1979.GammaU.FrameC

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.ResPair

theorem mem_map_conj_inv_iff {F : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (A l : V12 ≃ₗ[ZMod 2] V12) :
    l ∈ F.map (MulAut.conj A⁻¹).toMonoidHom ↔ A * l * A⁻¹ ∈ F := by
  rw [mem_map_conj]
  constructor
  · rintro ⟨k, hk, rfl⟩
    convert hk using 1
    group
  · intro h
    exact ⟨A * l * A⁻¹, h, by group⟩

theorem map_mul_map (S : Submodule (ZMod 2) V12) (A B : V12 ≃ₗ[ZMod 2] V12) :
    S.map ((A * B : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) =
      (S.map (B : V12 →ₗ[ZMod 2] V12)).map (A : V12 →ₗ[ZMod 2] V12) := by
  rw [← Submodule.map_comp]
  rfl

theorem frameCensus
    {i : ℕ} (hi : i = 0 ∨ i = 1) {x : V12}
    {D : Submodule (ZMod 2) V12} {F : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp x D F) :
    (∃ n ∈ n2 i, ∀ l, l ∈ F ↔ RowsSet (compOf i) (n⁻¹ * l * n)) ∨
      Violation (n2 i ⊔ F) (compOf i) (idR :: hyp10 i) := by
  classical
  have h1 := Certificates.certificate16963
  have h2 := Certificates.certificate16964
  have hFc := Certificates.certificate16982
  obtain ⟨T, m, hT, P, hPg, hNle, hcov, hpts⟩ := hFc i hi
  obtain ⟨g, hgP, U, hU, hxU⟩ := hcov x H.ne_zero H.q_eq
  subst hxU
  have hg := hPg g hgP
  obtain ⟨j, hj, -, -, hDj, -⟩ := frame_at h1 h2 T hT.1 hT.2.1 hT.2.2 (mul_mem (hNle hU) hg) H
  obtain ⟨M, hM, hMx, j', hj', hE, hgood⟩ := hpts g hgP j hj
  have hn : U * M ∈ n2 i := mul_mem hU hM
  have hT' := hT.1 j' hj'
  have hV : U * M * (g * T j') ∈ gammaU := mul_mem (hNle hn) (mul_mem hg hT'.1)
  have hVa : (U * M * (g * T j')) (vecOf a0) = U (g (vecOf a0)) := by
    change U (M (g (T j' (vecOf a0)))) = _
    rw [hT'.2, hMx]
  have hVD : (spanOf d0).map ((U * M * (g * T j') : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = D := by
    rw [hDj, mul_assoc U g (T j), map_mul_map _ U (g * T j), hE, map_mul_map _ (U * M) (g * T j'),
      map_mul_map _ U M]
  have H₂ := H.conj (inv_mem hV)
  have hVa' : (U * M * (g * T j'))⁻¹ (U (g (vecOf a0))) = vecOf a0 := by
    rw [← hVa, inv_apply_apply]
  rw [hVa', ← hVD, map_inv_map] at H₂
  obtain ⟨c, hc, hcL⟩ := comp_of_d0 h2 H₂
  have hmemF : ∀ l, l ∈ F ↔
      RowsSet (compOf c) ((U * M * (g * T j'))⁻¹ * l * (U * M * (g * T j'))) := fun l => by
    have h := hcL ((U * M * (g * T j'))⁻¹ * l * (U * M * (g * T j')))
    rw [mem_map_conj_inv_iff] at h
    have e : U * M * (g * T j') * ((U * M * (g * T j'))⁻¹ * l * (U * M * (g * T j'))) *
        (U * M * (g * T j'))⁻¹ = l := by group
    rw [e] at h
    exact h
  rcases hgood c hc with ⟨-, heq⟩ | hviol
  ·
    refine Or.inl ⟨U * M, hn, fun l => ?_⟩
    rw [hmemF, heq ((U * M)⁻¹ * l * (U * M))]
    have e : (U * M * (g * T j'))⁻¹ * l * (U * M * (g * T j')) =
        (g * T j')⁻¹ * ((U * M)⁻¹ * l * (U * M)) * (g * T j') := by group
    rw [e]
  ·
    right
    have hF' : ∀ l, l ∈ F.map (MulAut.conj (U * M)⁻¹).toMonoidHom ↔
        RowsSet (compOf c) ((g * T j')⁻¹ * l * (g * T j')) := fun l => by
      rw [mem_map_conj_inv_iff, hmemF]
      have e : (U * M * (g * T j'))⁻¹ * (U * M * l * (U * M)⁻¹) * (U * M * (g * T j')) =
          (g * T j')⁻¹ * l * (g * T j') := by group
      rw [e]
    have hsup : n2 i ⊔ F.map (MulAut.conj (U * M)⁻¹).toMonoidHom = n2 i ⊔ F := by
      apply le_antisymm
      · refine sup_le le_sup_left fun l hl => ?_
        rw [mem_map_conj_inv_iff] at hl
        have key := mul_mem (mul_mem (le_sup_left (a := n2 i) (b := F) (inv_mem hn))
          (le_sup_right (a := n2 i) hl)) (le_sup_left (a := n2 i) (b := F) hn)
        have e : (U * M)⁻¹ * (U * M * l * (U * M)⁻¹) * (U * M) = l := by group
        rwa [e] at key
      · refine sup_le le_sup_left fun l hl => ?_
        have hl' : (U * M)⁻¹ * l * (U * M) ∈ F.map (MulAut.conj (U * M)⁻¹).toMonoidHom := by
          rw [mem_map_conj_inv_iff]
          have e : U * M * ((U * M)⁻¹ * l * (U * M)) * (U * M)⁻¹ = l := by group
          rw [e]
          exact hl
        have key := mul_mem (mul_mem (le_sup_left (a := n2 i)
          (b := F.map (MulAut.conj (U * M)⁻¹).toMonoidHom) hn) (le_sup_right (a := n2 i) hl'))
          (le_sup_left (a := n2 i) (b := F.map (MulAut.conj (U * M)⁻¹).toMonoidHom) (inv_mem hn))
        have e : U * M * ((U * M)⁻¹ * l * (U * M)) * (U * M)⁻¹ = l := by group
        rwa [e] at key
    rw [← hsup]
    exact hviol _ hF'

end CFSG.GF2Type.Smith1979.GammaU.FrameC
