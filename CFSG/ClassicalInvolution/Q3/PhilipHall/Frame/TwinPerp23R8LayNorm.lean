module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Sigma

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lay

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Norm

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem normalizer_le_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    Subgroup.normalizer (W : Set Y) ≤ sigmaStarNorm (Om R) (tightCore R) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  obtain ⟨R₁, -, -, -, hR₁, -, hR₁D, -⟩ := e_decomp hc
  intro r hr
  refine T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK ?_
  by_cases h : conjSub r (tightCore R) = tightCore R
  · rw [h]
    exact Relation.ReflTransGen.refl
  · have hJ : conjSub r (tightCore R) ∈ Om R := hΩ.conjInvariant r _ hK
    have hT : conjSub r R₁ ∈ DSet (Om R) W := by
      refine ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hR₁D.1 r, fun x hx => ?_⟩
      rw [mem_conjSub_iff] at hx
      have h1 : r⁻¹ * x * r ∈ Subgroup.normalizer (W : Set Y) := hR₁D.2 hx
      have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hr h1) (Subgroup.inv_mem _ hr)
      simpa [mul_assoc] using h2
    have hnbr := Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hc.std.hW hK hJ (fun h' => h h'.symm)
      hR₁D hT hR₁ (hR₁.conj r)
    exact Relation.ReflTransGen.single ⟨hJ, Or.inl hnbr.1⟩

theorem g_mem_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    g ∈ sigmaStarNorm (Om R) (tightCore R) :=
  normalizer_le_sigmaStarNorm hc (T7K.g_mem_normalizer hc.data)

theorem conjSub_g_mem_dstarComp (hc : P23Cfg n Y R S t K' W u e g) :
    conjSub g (tightCore R) ∈ dstarComp (Om R) (tightCore R) :=
  ((mem_sigmaStarNorm_iff.mp (g_mem_sigmaStarNorm hc)) (tightCore R)).mp
    Relation.ReflTransGen.refl

theorem centralizer_ue_le_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    Subgroup.centralizer ({u * e} : Set Y) ≤ sigmaStarNorm (Om R) (tightCore R) :=
  T7A.centralizer_conj_le (g_mem_sigmaStarNorm hc) hc.data.hgt.symm
    (R56.centralizer_t_le_sigmaStarNorm hc)

theorem exists_mem_normalizer_conj_ue (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ k ∈ Subgroup.normalizer (W : Set Y), k * (u * e) * k⁻¹ = u * e * t := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, -, hcomm, hb₁R, hb'R', ob₁, -, hub, -⟩ := e_decomp hc
  have hQ : IsQuatSub R₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  obtain ⟨k, hkR, hkb, -, -⟩ := S16.isQuatSub_exists_inv hQ hb₁R
  have hkN : k ∈ Subgroup.normalizer (W : Set Y) := hRD.2 hkR
  have hke : k * e = e * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (normalizer_le_centralizer_e hd hkN)
  have hkb' : k * b' = b' * k := hcomm k hkR b' hb'R'
  have htb' : t * b' = b' * t := hz'.commute_of_mem (hR₁'.1 hb'R')
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hte : t * e = e * t := hWab t hd.hzW e (T7K.e_mem_inf hd).1
  have hb₁inv : b₁⁻¹ = b₁ * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ob₁, hz.sq])
  have h1 : k * b' * k⁻¹ = b' := by rw [hkb', mul_assoc, mul_inv_cancel, mul_one]
  have h2 : k * e * k⁻¹ = e := by rw [hke, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨k, hkN, ?_⟩
  calc k * (u * e) * k⁻¹ = (k * b₁ * k⁻¹) * (k * b' * k⁻¹) * (k * e * k⁻¹) := by rw [hub]; group
    _ = b₁⁻¹ * b' * e := by rw [hkb, h1, h2]
    _ = b₁ * (t * b') * e := by rw [hb₁inv]; group
    _ = b₁ * (b' * t) * e := by rw [htb']
    _ = b₁ * b' * (t * e) := by group
    _ = b₁ * b' * (e * t) := by rw [hte]
    _ = u * e * t := by rw [hub]; group

theorem centralizer_uet_le_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    Subgroup.centralizer ({u * e * t} : Set Y) ≤ sigmaStarNorm (Om R) (tightCore R) := by
  obtain ⟨k, hkN, hk⟩ := exists_mem_normalizer_conj_ue hc
  exact T7A.centralizer_conj_le (normalizer_le_sigmaStarNorm hc hkN) hk.symm
    (centralizer_ue_le_sigmaStarNorm hc)

end Norm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lay
