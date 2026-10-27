module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Proj
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.Coordinator.D4Bridge
  CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.Open CFSG.RankThree.Classical2

section Rho

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def rho : orthDerived Q →* ProjOrthDerived Q :=
  QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))

@[expose] def rhoImg (L : Subgroup (V ≃ₗ[K] V)) : Subgroup (ProjOrthDerived Q) :=
  (L.subgroupOf (orthDerived Q)).map (rho Q)

variable {Q}

theorem mem_rhoImg {L : Subgroup (V ≃ₗ[K] V)} {t : ProjOrthDerived Q} :
    t ∈ rhoImg Q L ↔ ∃ z : orthDerived Q, (z : V ≃ₗ[K] V) ∈ L ∧ rho Q z = t := by
  simp only [rhoImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem rhoImg_map_conj (g : orthDerived Q) (L : Subgroup (V ≃ₗ[K] V)) :
    rhoImg Q (L.map (MulAut.conj (g : V ≃ₗ[K] V)).toMonoidHom) =
      (rhoImg Q L).map (MulAut.conj (rho Q g)).toMonoidHom := by
  ext t
  rw [mem_rhoImg, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.1 hz
    have hlz' : (l : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V)⁻¹ * z * g := by
      rw [← hlz]
      simp [MulAut.conj_apply, mul_assoc]
    refine ⟨rho Q (g⁻¹ * z * g), mem_rhoImg.2 ⟨g⁻¹ * z * g, ?_, rfl⟩, ?_⟩
    · have : ((g⁻¹ * z * g : orthDerived Q) : V ≃ₗ[K] V) = l := by
        rw [hlz']
        simp
      rw [this]
      exact hl
    · simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨z, hz, rfl⟩ := mem_rhoImg.1 ht'
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨z, hz, ?_⟩
      simp [MulAut.conj_apply]
    · simp [MulAut.conj_apply, map_mul, map_inv]

end Rho

section Std

variable (K : Type) [Field K]

@[expose] def stdPair (i : Fin 4) : HypPair (quadPlus 4 K) where
  e := Pi.single (Sum.inl i) 1
  f := Pi.single (Sum.inr i) 1
  Q_e := D4Bridge.quadPlus_single _
  Q_f := D4Bridge.quadPlus_single _
  polar_ef := by
    rw [polar_single]
    simp [dualC]

theorem stdPair_orth {i j : Fin 4} (h : i ≠ j) : (stdPair K i).Orth (stdPair K j) where
  ee := polar_single_single (by simpa [cIdx] using h)
  ef := polar_single_single (by simpa [cIdx] using h)
  fe := polar_single_single (by simpa [cIdx] using h)
  ff := polar_single_single (by simpa [cIdx] using h)

theorem orthDerived_quadPlus_eq :
    orthDerived (quadPlus 4 K) = elementaryGroup (quadPlus 4 K) :=
  commutator_orthogonalGroup_quadPlus (by norm_num)

theorem nondegenerate_quadPlus_four : (QuadraticMap.polarBilin (quadPlus 4 K)).Nondegenerate :=
  (regular_quadPlus (K := K) (n := 4) (by norm_num)).1

theorem mem_elementary_of_mem_orthDerived {y : (Coord → K) ≃ₗ[K] (Coord → K)}
    (hy : y ∈ orthDerived (quadPlus 4 K)) : y ∈ elementaryGroup (quadPlus 4 K) := by
  rwa [orthDerived_quadPlus_eq] at hy

theorem mem_orthDerived_of_mem_elementary {y : (Coord → K) ≃ₗ[K] (Coord → K)}
    (hy : y ∈ elementaryGroup (quadPlus 4 K)) : y ∈ orthDerived (quadPlus 4 K) := by
  rwa [orthDerived_quadPlus_eq]

end Std

section P


variable (K : Type) [Field K] [Finite K]

theorem eTheta_rho (z : orthDerived (quadPlus 4 K)) :
    eTheta K (rho (quadPlus 4 K) z) =
      theta K ⟨(z : (Coord → K) ≃ₗ[K] (Coord → K)), mem_elementary_of_mem_orthDerived K z.2⟩ := by
  set A : StatedOmega (StatedQuadPlus 4 K) :=
    (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.omegaOrthEquiv (coe_quadPlus 4 K)).symm z
    with hA
  have h1 : CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.omegaOrthEquiv (coe_quadPlus 4 K) A = z :=
    MulEquiv.apply_symm_apply _ _
  have h2 := eTheta_mk K A
  rw [h1] at h2
  refine h2.trans ?_
  show theta K (omegaEquiv K A) = _
  congr 1
  apply Subtype.ext
  have h3 := congrArg (fun w : orthDerived (quadPlus 4 K) => (w : (Coord → K) ≃ₗ[K] (Coord → K))) h1
  exact h3

@[expose] def Pimg (L : Subgroup ((Coord → K) ≃ₗ[K] (Coord → K))) :
    Subgroup (adjointGroup Tag.D4 K) :=
  (rhoImg (quadPlus 4 K) L).map (eTheta K).toMonoidHom

variable {K}

theorem Pimg_map_subtype (M : Subgroup (elementaryGroup (quadPlus 4 K))) :
    Pimg K (M.map (elementaryGroup (quadPlus 4 K)).subtype) = M.map (theta K) := by
  ext P
  simp only [Pimg, Subgroup.mem_map, mem_rhoImg]
  constructor
  · rintro ⟨_, ⟨z, ⟨m, hm, hmz⟩, rfl⟩, rfl⟩
    refine ⟨m, hm, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, eTheta_rho]
    congr 1
    exact Subtype.ext hmz
  · rintro ⟨m, hm, rfl⟩
    refine ⟨rho (quadPlus 4 K) ⟨m.1, mem_orthDerived_of_mem_elementary K m.2⟩,
      ⟨⟨m.1, mem_orthDerived_of_mem_elementary K m.2⟩, ⟨m, hm, rfl⟩, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, eTheta_rho]

theorem Pimg_map_conj {g : (Coord → K) ≃ₗ[K] (Coord → K)} (hg : g ∈ elementaryGroup (quadPlus 4 K))
    (L : Subgroup ((Coord → K) ≃ₗ[K] (Coord → K))) :
    Pimg K (L.map (MulAut.conj g).toMonoidHom) =
      (Pimg K L).map (MulAut.conj (theta K ⟨g, hg⟩)).toMonoidHom := by
  have h1 := rhoImg_map_conj (Q := quadPlus 4 K) ⟨g, mem_orthDerived_of_mem_elementary K hg⟩ L
  simp only [Pimg]
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  have h2 : (eTheta K).toMonoidHom.comp (MulAut.conj (rho (quadPlus 4 K)
      ⟨g, mem_orthDerived_of_mem_elementary K hg⟩)).toMonoidHom =
      (MulAut.conj (theta K ⟨g, hg⟩)).toMonoidHom.comp (eTheta K).toMonoidHom := by
    ext t
    have := eTheta_rho K ⟨g, mem_orthDerived_of_mem_elementary K hg⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      this]
  rw [h2]

variable (K)

theorem Pimg_leviV_std :
    Pimg K (leviV (quadPlus 4 K) (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inl 1) 1)
      (Pi.single (Sum.inr 0) 1) (Pi.single (Sum.inr 1) 1)) =
      simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0 := by
  rw [← leviE_map_subtype, Pimg_map_subtype, theta_leviE_node0]

theorem exists_Pimg_levi_eq_root {A B : HypPair (quadPlus 4 K)} (h : A.Orth B) :
    ∃ c : adjointGroup Tag.D4 K, Pimg K (levi (quadPlus 4 K) A B) =
      (simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0).map
        (MulAut.conj c).toMonoidHom := by
  obtain ⟨g, hg, hgl⟩ := exists_levi_conj (nondegenerate_quadPlus_four K)
    (stdPair_orth K (show (0 : Fin 4) ≠ 1 by decide)) (stdPair_orth K (show (0 : Fin 4) ≠ 2 by decide))
    (stdPair_orth K (show (1 : Fin 4) ≠ 2 by decide)) h
  refine ⟨theta K ⟨g, hg⟩, ?_⟩
  rw [hgl, Pimg_map_conj hg, ← Pimg_leviV_std]
  rfl

end P

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
