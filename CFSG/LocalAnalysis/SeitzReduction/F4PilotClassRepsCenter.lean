module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassReps

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {K : Type} [Field K]

namespace ClassReps

@[expose] def corootOne : Fin Tag.F4.rank → ℤ := ![2, -1, 0, 0]

@[expose] def corootFour : Fin Tag.F4.rank → ℤ := ![0, 0, -1, 2]

theorem f4Pairing_rootR_rootS :
    f4Pairing corootOne (orbitCertRoot .F4 47) = 1 ∧
      f4Pairing corootOne (orbitCertRoot .F4 44) = 0 ∧
      f4Pairing corootFour (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing corootFour (orbitCertRoot .F4 44) = 1 := by
  decide +kernel

theorem exists_rootChar_eq (A B : Kˣ) : ∃ a : Fin Tag.F4.rank → Kˣ,
    rootChar a (orbitCertRoot .F4 47) = A ∧ rootChar a (orbitCertRoot .F4 44) = B := by
  obtain ⟨h1, h2, h3, h4⟩ := f4Pairing_rootR_rootS
  refine ⟨(fun i : Fin Tag.F4.rank => A ^ corootOne i) *
    (fun i : Fin Tag.F4.rank => B ^ corootFour i), ?_, ?_⟩
  · rw [rootChar_mul_tuple, rootChar_zpow, rootChar_zpow, h1, h3, zpow_one, zpow_zero, mul_one]
  · rw [rootChar_mul_tuple, rootChar_zpow, rootChar_zpow, h2, h4, zpow_one, zpow_zero, one_mul]

section Center


theorem exists_eq_f4x_44_mul_f4x_47_of_commute [Finite K] [CharP K 2] {g : adjointGroup .F4 K}
    (hg : ∀ u ∈ posUnipotent .F4 K, (g : ModGL .F4 K) * u = u * g) :
    ∃ c d : K, (g : ModGL .F4 K) = f4x K 44 c * f4x K 47 d := by
  have hA : MulAut.conj g ∈ diagonalFieldActors .F4 K :=
    (Chevalley_diagonal_field_actor_data.1 .F4 K).2.2 ⟨g, rfl⟩
  obtain ⟨u, hu, huC, hgu⟩ := exists_eq_conj_of_mem_actors_of_fix_heightSeries hA fun x hx => by
    rw [MulAut.conj_apply]
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg x (heightSeries_le_posUnipotent 3 hx), mul_inv_cancel_right]
  have hg' : g = ⟨u, huC⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.conj_injective center_adjointGroup_eq_bot hgu
  have hgU : (g : ModGL .F4 K) ∈ posUnipotent .F4 K := by
    rw [hg']
    exact hu
  obtain ⟨c, d, h⟩ := CFSG.Monster.B.GSide.f4_mem_of_commute_rootElts hgU fun p hp hp' => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hg _ (f4x_mem_posUnipotent ⟨hp, hp'⟩ 1)
  exact ⟨c, d, h.symm⟩

theorem f4x_44_mul_f4x_47_commute [CharP K 2] (c d : K) {u : ModGL .F4 K}
    (hu : u ∈ posUnipotent .F4 K) :
    f4x K 44 c * f4x K 47 d * u = u * (f4x K 44 c * f4x K 47 d) := by
  have h1 := f4x_central (Or.inr rfl) d hu
  have h2 := f4x_central (Or.inl rfl) c hu
  calc f4x K 44 c * f4x K 47 d * u = f4x K 44 c * (u * f4x K 47 d) := by rw [mul_assoc, h1]
    _ = u * f4x K 44 c * f4x K 47 d := by rw [← mul_assoc, ← h2]
    _ = u * (f4x K 44 c * f4x K 47 d) := by rw [mul_assoc]

theorem rootDiagUnit_conj_f4x_44_mul_f4x_47 (a : Fin Tag.F4.rank → Kˣ) (c d : K) :
    rootDiagUnit .F4 a * (f4x K 44 c * f4x K 47 d) * (rootDiagUnit .F4 a)⁻¹ =
      f4x K 44 ((rootChar a (orbitCertRoot .F4 44) : K) * c) *
        f4x K 47 ((rootChar a (orbitCertRoot .F4 47) : K) * d) := by
  have e44 := rootDiagUnit_conj_pinnedX a (f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩).1 c
  have e47 := rootDiagUnit_conj_pinnedX a (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1 d
  simp only [f4x]
  rw [← e44, ← e47]
  group

theorem exists_rootDiagUnit_conj_eq_frame [CharP K 2] {c d : K}
    (h : f4x K 44 c * f4x K 47 d ≠ 1) : ∃ a : Fin Tag.F4.rank → Kˣ,
      rootDiagUnit .F4 a * (f4x K 44 c * f4x K 47 d) * (rootDiagUnit .F4 a)⁻¹ = f4x K 47 1 ∨
      rootDiagUnit .F4 a * (f4x K 44 c * f4x K 47 d) * (rootDiagUnit .F4 a)⁻¹ = f4x K 44 1 ∨
      rootDiagUnit .F4 a * (f4x K 44 c * f4x K 47 d) * (rootDiagUnit .F4 a)⁻¹ =
        f4x K 47 1 * f4x K 44 1 := by
  classical
  have hunit : ∀ e : K, ∃ E : Kˣ, (E : K) * e = if e = 0 then 0 else 1 := fun e => by
    by_cases he : e = 0
    · exact ⟨1, by rw [he, ite_eq_left rfl, mul_zero]⟩
    · exact ⟨(Units.mk0 e he)⁻¹, by
        rw [ite_eq_right he, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ he]⟩
  obtain ⟨A, hA⟩ := hunit d
  obtain ⟨B, hB⟩ := hunit c
  obtain ⟨a, ha47, ha44⟩ := exists_rootChar_eq A B
  refine ⟨a, ?_⟩
  rw [rootDiagUnit_conj_f4x_44_mul_f4x_47, ha47, ha44, hA, hB]
  have hcomm : f4x K 44 1 * f4x K 47 1 = f4x K 47 1 * f4x K 44 1 :=
    f4x_central (Or.inr rfl) 1 (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ 1)
  by_cases hc : c = 0
  · by_cases hd : d = 0
    · exfalso
      apply h
      rw [hc, hd, f4x_zero, f4x_zero, one_mul]
    · left
      rw [ite_eq_left hc, ite_eq_right hd, f4x_zero, one_mul]
  · by_cases hd : d = 0
    · right; left
      rw [ite_eq_right hc, ite_eq_left hd, f4x_zero, mul_one]
    · right; right
      rw [ite_eq_right hc, ite_eq_right hd, hcomm]

noncomputable def posUnipotentSylow [Finite K] [CharP K 2] : Sylow 2 (adjointGroup .F4 K) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
      (card_posUnipotent (τ := .F4) (K := K))).1.toSylow
    (isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
      (card_posUnipotent (τ := .F4) (K := K))).2

theorem mem_posUnipotentSylow [Finite K] [CharP K 2] {x : adjointGroup .F4 K} :
    x ∈ (posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)) ↔
      (x : ModGL .F4 K) ∈ posUnipotent .F4 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [posUnipotentSylow, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]

theorem exists_conj_eq_f4x_44_mul_f4x_47_of_mem_centralizer [Finite K] [CharP K 2]
    (U : Sylow 2 (adjointGroup .F4 K)) {z : adjointGroup .F4 K}
    (hz : z ∈ centralizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K))) :
    ∃ g : adjointGroup .F4 K, (U : Subgroup (adjointGroup .F4 K)) =
        (posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)).map
          (MulAut.conj g).toMonoidHom ∧
      ∃ c d : K, ((g⁻¹ * z * g : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 44 c * f4x K 47 d := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .F4 K) (posUnipotentSylow (K := K)) U
  have hU : (U : Subgroup (adjointGroup .F4 K)) =
      (posUnipotentSylow (K := K) : Subgroup (adjointGroup .F4 K)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_smul_sylow_eq_map]
  refine ⟨g, hU, exists_eq_f4x_44_mul_f4x_47_of_commute fun u hu => ?_⟩
  have huC : u ∈ adjointGroup .F4 K := posUnipotent_le_adjointGroup hu
  have hmem : g * ⟨u, huC⟩ * g⁻¹ ∈ (U : Subgroup (adjointGroup .F4 K)) := by
    rw [hU]
    exact ⟨⟨u, huC⟩, mem_posUnipotentSylow.2 hu, rfl⟩
  have hc := mem_centralizer_iff.1 hz _ hmem
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc' ⊢
  calc (g : ModGL .F4 K)⁻¹ * z * g * u =
        (g : ModGL .F4 K)⁻¹ * (z * (g * u * (g : ModGL .F4 K)⁻¹)) * g := by group
    _ = (g : ModGL .F4 K)⁻¹ * ((g * u * (g : ModGL .F4 K)⁻¹) * z) * g := by rw [hc']
    _ = u * ((g : ModGL .F4 K)⁻¹ * z * g) := by group

theorem centralizer_sylow_le [Finite K] [CharP K 2] (U : Sylow 2 (adjointGroup .F4 K)) :
    centralizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) ≤ U := by
  intro z hz
  obtain ⟨g, hU, c, d, hcd⟩ := exists_conj_eq_f4x_44_mul_f4x_47_of_mem_centralizer U hz
  rw [hU]
  refine ⟨g⁻¹ * z * g, mem_posUnipotentSylow.2 ?_, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩
  rw [hcd]
  exact mul_mem (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ c)
    (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ d)

end Center

end ClassReps

section FactF2


open ClassReps

theorem factF2 [Finite K] [CharP K 2] : FactF2 K := by
  intro U z hz hz1
  obtain ⟨g, -, c, d, hcd⟩ := exists_conj_eq_f4x_44_mul_f4x_47_of_mem_centralizer U hz
  have hne : f4x K 44 c * f4x K 47 d ≠ 1 := by
    rw [← hcd]
    intro h1
    apply hz1
    have h1' : g⁻¹ * z * g = 1 := Subtype.ext h1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1']; group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_conj_eq_frame hne
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  obtain ⟨haC, -⟩ := (hrest B hB a).2.2
  set h : adjointGroup .F4 K := ⟨rootDiagUnit .F4 a, haC⟩
  obtain ⟨hT, hU, hTU, -⟩ := weylEltC_conj_frame (K := K)
  set n := weylEltC K weylWordT
  have key : ∀ {w y' : adjointGroup .F4 K},
      (h : ModGL .F4 K) * (f4x K 44 c * f4x K 47 d) * (h : ModGL .F4 K)⁻¹ = w →
      n * w * n⁻¹ = y' → (n * h * g⁻¹) * z * (n * h * g⁻¹)⁻¹ = y' := by
    intro w y' h1 h2
    rw [← h2]
    have h1' : h * (g⁻¹ * z * g) * h⁻¹ = w := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcd ⊢
      rw [hcd]
      exact h1
    rw [← h1']
    group
  rcases ha with ha | ha | ha
  · exact ⟨.t, _, key (w := frameT K) ha hT⟩
  · exact ⟨.u, _, key (w := frameU K) ha hU⟩
  · exact ⟨.tu, _, key (w := frameTU K) ha hTU⟩

end FactF2

end CFSG.SeitzReduction.F4Pilot
