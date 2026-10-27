module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutL
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Subgroup LinearOut
open scoped commutatorElement

variable {K : Type*} [Field K]

theorem range_conjAut_normal [Finite K] :
    ((conjAut 4 K : GL (Fin 4) K →* MulAut (projectiveSL 4 K)).range).Normal := by
  obtain ⟨-, -, hfc, hδδ, hδc, -, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  have hδinv : (dualAut 4 K)⁻¹ = dualAut 4 K := inv_eq_of_mul_eq_one_right hδδ
  constructor
  rintro _ ⟨A, rfl⟩ g
  have hgen := (automorphism_generation (K := K) (n := 4) (by norm_num)).2
  obtain ⟨B, σ, ε, hε, rfl⟩ := hgen g
  have h1 : ∀ C : GL (Fin 4) K, fieldAut 4 K σ * conjAut 4 K C * (fieldAut 4 K σ)⁻¹ ∈
      (conjAut 4 K).range := fun C => ⟨_, (hfc σ C).symm⟩
  have h2 : ∀ C : GL (Fin 4) K, dualAut 4 K * conjAut 4 K C * (dualAut 4 K)⁻¹ ∈
      (conjAut 4 K).range := fun C => ⟨_, by rw [hδinv]; exact (hδc C).symm⟩
  interval_cases ε
  · obtain ⟨C, hC⟩ := h1 A
    refine ⟨B * C * B⁻¹, ?_⟩
    rw [pow_zero, mul_one, map_mul, map_mul, map_inv, hC, _root_.mul_inv_rev]
    group
  · obtain ⟨C, hC⟩ := h2 A
    obtain ⟨C', hC'⟩ := h1 C
    refine ⟨B * C' * B⁻¹, ?_⟩
    rw [pow_one, map_mul, map_mul, map_inv, hC', hC, _root_.mul_inv_rev, _root_.mul_inv_rev]
    group

theorem commutator_mem_range_conjAut [Finite K] (u v : MulAut (projectiveSL 4 K)) :
    ⁅u, v⁆ ∈ (conjAut 4 K).range := by
  classical
  set N := (conjAut 4 K : GL (Fin 4) K →* MulAut (projectiveSL 4 K)).range with hN
  have hNn : N.Normal := range_conjAut_normal
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
  obtain ⟨-, -, hfc, hδδ, hδc, hδf, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  set S : Set (MulAut (projectiveSL 4 K)) :=
    Set.range (conjAut 4 K) ∪ Set.range (fieldAut 4 K) ∪ {dualAut 4 K} with hS
  have hSt : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro α _
    obtain ⟨A, σ, ε, -, rfl⟩ := hgen α
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (Or.inl ⟨A, rfl⟩)))
      (Subgroup.subset_closure (Or.inl (Or.inr ⟨σ, rfl⟩))))
      (pow_mem (Subgroup.subset_closure (show dualAut 4 K ∈ S from Or.inr rfl)) _)
  have hNsymm : ∀ x y : MulAut (projectiveSL 4 K), ⁅x, y⁆ ∈ N → ⁅y, x⁆ ∈ N := fun x y h => by
    have := inv_mem h
    rwa [commutatorElement_inv] at this
  have hδinv : (dualAut 4 K)⁻¹ = dualAut 4 K := inv_eq_of_mul_eq_one_right hδδ
  have hcc : ∀ A B : GL (Fin 4) K, ⁅conjAut 4 K A, conjAut 4 K B⁆ ∈ N := fun A B =>
    ⟨⁅A, B⁆, by rw [map_commutatorElement]⟩
  have hcf : ∀ (A : GL (Fin 4) K) (σ : K ≃+* K), ⁅conjAut 4 K A, fieldAut 4 K σ⁆ ∈ N := by
    intro A σ
    refine ⟨A * GeneralLinearGroup.map (σ : K →+* K) A⁻¹, ?_⟩
    rw [commutatorElement_def, mul_assoc (conjAut 4 K A), mul_assoc (conjAut 4 K A),
      ← map_inv (conjAut 4 K) A, hfc σ A⁻¹, map_mul]
  have hcδ : ∀ A : GL (Fin 4) K, ⁅conjAut 4 K A, dualAut 4 K⁆ ∈ N := by
    intro A
    refine ⟨A * GeneralLinearGroup.inverseTranspose A⁻¹, ?_⟩
    rw [commutatorElement_def, hδinv, mul_assoc (conjAut 4 K A), mul_assoc (conjAut 4 K A),
      ← map_inv (conjAut 4 K) A, hδc A⁻¹, map_mul]
  have hff : ∀ σ τ : K ≃+* K, ⁅fieldAut 4 K σ, fieldAut 4 K τ⁆ ∈ N := by
    intro σ τ
    rw [← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (ringAut_mul_comm K σ τ),
      map_one]
    exact one_mem N
  have hfδ : ∀ σ : K ≃+* K, ⁅fieldAut 4 K σ, dualAut 4 K⁆ ∈ N := by
    intro σ
    have h1 : ⁅fieldAut 4 K σ, dualAut 4 K⁆ = 1 := by
      rw [commutatorElement_def, hδinv, mul_assoc (fieldAut 4 K σ), mul_assoc (fieldAut 4 K σ),
        ← map_inv (fieldAut 4 K) σ, hδf σ⁻¹, map_inv, mul_inv_cancel]
    rw [h1]
    exact one_mem N
  refine commutator_mem_of_closure_eq_top N hSt ?_ u v
  rintro x ((⟨A, rfl⟩ | ⟨σ, rfl⟩) | hx) y ((⟨B, rfl⟩ | ⟨τ, rfl⟩) | hy)
  · exact hcc A B
  · exact hcf A τ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hcδ A
  · exact hNsymm _ _ (hcf B σ)
  · exact hff σ τ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hfδ σ
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hNsymm _ _ (hcδ B)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hNsymm _ _ (hfδ τ)
  · rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy, commutatorElement_self]
    exact one_mem N

theorem commutator_conjAut_mem_range_conj (A B : GL (Fin 4) K) :
    ⁅conjAut 4 K A, conjAut 4 K B⁆ ∈
      (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  rw [← map_commutatorElement]
  apply conjAut_mem_range_of_det _ 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), one_pow]

theorem le_range_conj_of_perfect [Finite K] {J : Subgroup (MulAut (projectiveSL 4 K))}
    (hJ : ⁅J, J⁆ = J) :
    J ≤ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  have h1 : J ≤ (conjAut 4 K).range := by
    rw [← hJ, commutator_le]
    intro u _ v _
    exact commutator_mem_range_conjAut u v
  rw [← hJ, commutator_le]
  intro u hu v hv
  obtain ⟨A, rfl⟩ := h1 hu
  obtain ⟨B, rfl⟩ := h1 hv
  exact commutator_conjAut_mem_range_conj A B

end DiagL

namespace AZ

open Subgroup

theorem le_of_perfect_of_le_inner {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (hC : centralizer (L : Set H) = ⊥)
    (hinn : ∀ J : Subgroup (MulAut L), ⁅J, J⁆ = J → J ≤ (MulAut.conj : L →* MulAut L).range)
    {J : Subgroup H} (hJ : ⁅J, J⁆ = J) : J ≤ L := by
  intro j hj
  set c : H →* MulAut L := MulAut.conjNormal with hc
  have hJ' : ⁅J.map c, J.map c⁆ = J.map c := by
    rw [← map_commutator, hJ]
  obtain ⟨l, hl⟩ := hinn _ hJ' ⟨j, hj, rfl⟩
  have h2 : (l : H)⁻¹ * j ∈ centralizer (L : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h3 := congrArg (fun ψ : MulAut L => ((ψ ⟨x, hx⟩ : L) : H)) hl
    simp only [hc, MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h3
    calc x * ((l : H)⁻¹ * j) = (l : H)⁻¹ * ((l : H) * x * (l : H)⁻¹) * j := by group
      _ = (l : H)⁻¹ * (j * x * j⁻¹) * j := by rw [h3]
      _ = (l : H)⁻¹ * j * x := by group
  rw [hC, mem_bot, inv_mul_eq_one] at h2
  rw [← h2]
  exact l.2

theorem le_inner_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ J : Subgroup (MulAut Y), ⁅J, J⁆ = J → J ≤ (MulAut.conj : Y →* MulAut Y).range)
    (J : Subgroup (MulAut X)) (hJ : ⁅J, J⁆ = J) :
    J ≤ (MulAut.conj : X →* MulAut X).range := by
  intro u hu
  have hJ' : ⁅J.map (MulAut.congr e).toMonoidHom, J.map (MulAut.congr e).toMonoidHom⁆ =
      J.map (MulAut.congr e).toMonoidHom := by rw [← map_commutator, hJ]
  obtain ⟨y, hy⟩ := hY _ hJ' ⟨u, hu, rfl⟩
  refine ⟨e.symm y, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut Y => φ (e x)) hy
  have h2 : ((MulAut.congr e).toMonoidHom u) (e x) = e (u x) := by
    change e (u (e.symm (e x))) = e (u x)
    rw [MulEquiv.symm_apply_apply]
  simp only [MulAut.conj_apply] at h1
  rw [h2] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end AZ

end CFSG.ComponentClassification.CatFactsL4U4
