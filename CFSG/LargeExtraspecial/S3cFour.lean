module

public import CFSG.LargeExtraspecial.S3cSetting
public import CFSG.LargeExtraspecial.S3bElevenFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem q_eq_one_of_mem_LbarLin_of_eq_eichler {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {t : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (ht : t ∈ S.LbarLin g) (ht1 : t ≠ 1) {u : S.Qt}
    (hau : polar S.q (S.cl (g * S.z * g⁻¹)) u = 0)
    (htu : t = eichler S.q (S.cl (g * S.z * g⁻¹)) u) : S.q u = 1 := by
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  have hu : u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro hu
    apply ht1
    rw [htu, (eichler_eq_one_iff S.q_nondegenerate ha0 haq hau).mpr hu]
  have htypes := eichler_type_of_not_mem_span S.q_nondegenerate ha0 haq hau hu
  rcases zmod2_eq_zero_or_eq_one (S.q u) with h | h
  · exfalso
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
    have hyQ : (y : G) ∉ S.QG := fun h' => ht1 (by
      rw [(S.ρ_eq_one_iff y).mpr h']
      rfl)
    have hA := htypes.2.1 h
    rw [← htu] at hA
    exact hno (S.hasTypeAInL_of_mem_L0 hy hyQ hA)
  · exact h

theorem exists_eichler_of_mem_LbarLin {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {t : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (htN : t ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))) :
    ∃ u, polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 ∧ t = eichler S.q (S.cl (g * S.z * g⁻¹)) u :=
  (mem_pointRadical_iff S.q_nondegenerate (S.cl_conj_z_ne_zero haQ hne)
    (S.q_cl_conj_z haQ)).mp htN

theorem false_of_three_mem_pointRadical {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {s₁ s₂ s₃ : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (h₁ : s₁ ∈ S.LbarLin g) (h₂ : s₂ ∈ S.LbarLin g) (h₃ : s₃ ∈ S.LbarLin g)
    (hN₁ : s₁ ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hN₂ : s₂ ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hN₃ : s₃ ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (n₁ : s₁ ≠ 1) (n₂ : s₂ ≠ 1) (n₃ : s₃ ≠ 1) (n₁₂ : s₁ * s₂ ≠ 1) (n₁₃ : s₁ * s₃ ≠ 1)
    (n₂₃ : s₂ * s₃ ≠ 1) (n₁₂₃ : s₁ * s₂ * s₃ ≠ 1) : False := by
  obtain ⟨u₁, hu₁, rfl⟩ := S.exists_eichler_of_mem_LbarLin haQ hne hN₁
  obtain ⟨u₂, hu₂, rfl⟩ := S.exists_eichler_of_mem_LbarLin haQ hne hN₂
  obtain ⟨u₃, hu₃, rfl⟩ := S.exists_eichler_of_mem_LbarLin haQ hne hN₃
  have key := fun {t} (ht : t ∈ S.LbarLin g) (ht1 : t ≠ 1) {u} hu htu =>
    S.q_eq_one_of_mem_LbarLin_of_eq_eichler haQ hne hno (t := t) ht ht1 (u := u) hu htu
  have hu₁₂ : polar S.q (S.cl (g * S.z * g⁻¹)) (u₁ + u₂) = 0 := by
    rw [polar_add_right, hu₁, hu₂, add_zero]
  have hu₁₃ : polar S.q (S.cl (g * S.z * g⁻¹)) (u₁ + u₃) = 0 := by
    rw [polar_add_right, hu₁, hu₃, add_zero]
  have hu₂₃ : polar S.q (S.cl (g * S.z * g⁻¹)) (u₂ + u₃) = 0 := by
    rw [polar_add_right, hu₂, hu₃, add_zero]
  have hu₁₂₃ : polar S.q (S.cl (g * S.z * g⁻¹)) (u₁ + u₂ + u₃) = 0 := by
    rw [polar_add_right, hu₁₂, hu₃, add_zero]
  exact false_of_three_anisotropic (key h₁ n₁ hu₁ rfl) (key h₂ n₂ hu₂ rfl) (key h₃ n₃ hu₃ rfl)
    (key (mul_mem h₁ h₂) n₁₂ hu₁₂ (eichler_mul hu₁ hu₂))
    (key (mul_mem h₁ h₃) n₁₃ hu₁₃ (eichler_mul hu₁ hu₃))
    (key (mul_mem h₂ h₃) n₂₃ hu₂₃ (eichler_mul hu₂ hu₃))
    (key (mul_mem (mul_mem h₁ h₂) h₃) n₁₂₃ hu₁₂₃ (by
      rw [eichler_mul hu₁ hu₂, eichler_mul hu₁₂ hu₃]))

theorem exists_polar_cl_eq_one {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ v, polar S.q (S.cl (g * S.z * g⁻¹)) v = 1 := by
  obtain ⟨v, hv⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero S.q_nondegenerate
    (S.cl_conj_z_ne_zero haQ hne)
  exact ⟨v, zmod2_eq_one_of_ne_zero hv⟩

theorem finrank_clSub_of_irreducible (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width :=
  ((S.lemma_3_11_two hTI hn haQ hne hno).resolve_left hirr).2.2.2.1

theorem Lbar_inf_pointRadical_of_width_eq_four (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 4) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {s : S.O} (hs : s ∈ S.Lbar g)
    (hsN : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))) : s = 1 := by
  have C := S.transvectionConfig hTI (by omega) haQ hne hno hirr
  obtain ⟨v, hv⟩ := S.exists_polar_cl_eq_one haQ hne
  have hW := S.finrank_clSub_of_irreducible hTI (by omega) haQ hne hno hirr
  have hK : finrank (ZMod 2) C.K = 3 := by
    have := C.finrank_K_add_one
    omega
  by_contra hs1
  obtain ⟨φ₀, hφ₀⟩ := C.exists_sOf_eq (S.coe_mem_LbarLin hs)
  have hφ₀0 : φ₀ ≠ 0 := fun h => hs1 (Subtype.ext (by rw [← hφ₀, h, C.sOf_zero]; rfl))
  have hrad₀ : ∀ ψ χ, C.theta v φ₀ ψ χ = 0 :=
    C.theta_eq_zero_of_mem_pointRadical v (hφ₀ ▸ hsN)
  have hzero := (C.isAltTrilin_theta v).eq_zero_of_finrank_eq_three hK hφ₀0 hrad₀
  have hN : ∀ φ, C.sOf φ ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := fun φ =>
    C.mem_pointRadical_of_theta_eq_zero S.q_nondegenerate hv fun ψ χ => hzero φ ψ χ
  set b := Module.finBasisOfFinrankEq (ZMod 2) C.K hK with hb
  have hne1 : ∀ φ : C.K, φ ≠ 0 → C.sOf φ ≠ 1 := fun φ hφ h => hφ ((C.sOf_eq_one_iff φ).mp h)
  have hrepr : ∀ (c : Fin 3 → ZMod 2) (i : Fin 3),
      b.repr (c 0 • b 0 + c 1 • b 1 + c 2 • b 2) i = c i := by
    intro c i
    fin_cases i <;> simp
  have hnz : ∀ c : Fin 3 → ZMod 2, c ≠ 0 → c 0 • b 0 + c 1 • b 1 + c 2 • b 2 ≠ 0 := by
    intro c hc h0
    apply hc
    funext i
    rw [← hrepr c i, h0, map_zero, Finsupp.zero_apply, Pi.zero_apply]
  have e : ∀ (c : Fin 3 → ZMod 2), c ≠ 0 → C.sOf (c 0 • b 0 + c 1 • b 1 + c 2 • b 2) ≠ 1 :=
    fun c hc => hne1 _ (hnz c hc)
  refine S.false_of_three_mem_pointRadical haQ hne hno (C.sOf_mem (b 0)) (C.sOf_mem (b 1))
    (C.sOf_mem (b 2)) (hN _) (hN _) (hN _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using e ![1, 0, 0] (by decide)
  · simpa using e ![0, 1, 0] (by decide)
  · simpa using e ![0, 0, 1] (by decide)
  · have := e ![1, 1, 0] (by decide)
    simpa [C.sOf_add] using this
  · have := e ![1, 0, 1] (by decide)
    simpa [C.sOf_add] using this
  · have := e ![0, 1, 1] (by decide)
    simpa [C.sOf_add] using this
  · have := e ![1, 1, 1] (by decide)
    simpa [C.sOf_add, mul_assoc] using this

theorem fixLbar_eq_span_of_width_eq_four (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 4) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) :
    S.fixLbar g = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) :=
  S.fixLbar_eq_span_of_pointRadical (by omega) haQ hne fun _ hs hsN =>
    S.Lbar_inf_pointRadical_of_width_eq_four hTI hn haQ hne hno hirr hs hsN

end Setting

end CFSG.LargeExtraspecial
