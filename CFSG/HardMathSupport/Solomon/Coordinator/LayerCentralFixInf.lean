module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Fix

variable {K Q : Type} [Group K] [Group Q] {ι : Type*}

theorem map_iInf_fixSubgroup_le (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k)) :
    (⨅ i, fixSubgroup (α i)).map π ≤ ⨅ i, fixSubgroup (β i) :=
  le_iInf fun i =>
    (Subgroup.map_mono (iInf_le _ i)).trans (map_fixSubgroup_le π hker (α i) (β i) (hαβ i))

theorem conj_mem_iInf_fixSubgroup (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    {k f : K} (hk : π k ∈ ⨅ i, fixSubgroup (β i)) (hf : f ∈ ⨅ i, fixSubgroup (α i)) :
    k * f * k⁻¹ ∈ ⨅ i, fixSubgroup (α i) :=
  Subgroup.mem_iInf.2 fun i =>
    conj_mem_fixSubgroup π hker (α i) (β i) (hαβ i) (Subgroup.mem_iInf.1 hk i)
      (Subgroup.mem_iInf.1 hf i)

theorem comm_mem_iInf_fixSubgroup (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    {k₁ k₂ : K} (h₁ : π k₁ ∈ ⨅ i, fixSubgroup (β i)) (h₂ : π k₂ ∈ ⨅ i, fixSubgroup (β i)) :
    ⁅k₁, k₂⁆ ∈ ⨅ i, fixSubgroup (α i) :=
  Subgroup.mem_iInf.2 fun i =>
    comm_mem_fixSubgroup π hker (α i) (β i) (hαβ i) (Subgroup.mem_iInf.1 h₁ i)
      (Subgroup.mem_iInf.1 h₂ i)

theorem kerCentral_iInf_fixSubgroup (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) :
    ∀ y ∈ (⨅ i, fixSubgroup (α i)) ⊓ π.ker, ∀ x ∈ ⨅ i, fixSubgroup (α i), x * y = y * x :=
  fun _ hy x _ => Subgroup.mem_center_iff.1 (hker hy.2) x

theorem normal_map_iInf_fixSubgroup (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    (hπ : Function.Surjective π) :
    (((⨅ i, fixSubgroup (α i)).map π).subgroupOf (⨅ i, fixSubgroup (β i))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨k, hk⟩ := hπ (g : Q)
  have hkg : π k ∈ ⨅ i, fixSubgroup (β i) := by rw [hk]; exact g.2
  refine ⟨k * f * k⁻¹, conj_mem_iInf_fixSubgroup π hker α β hαβ hkg hf, ?_⟩
  simp only [map_mul, map_inv, hk, hfx]
  rfl

theorem le_map_iInf_fixSubgroup_of_perfect (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    (hπ : Function.Surjective π) {A : Subgroup Q} (hA : A ≤ ⨅ i, fixSubgroup (β i))
    (hperf : ⁅A, A⁆ = A) : A ≤ (⨅ i, fixSubgroup (α i)).map π := by
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro a₁ ha₁ a₂ ha₂
  obtain ⟨k₁, rfl⟩ := hπ a₁
  obtain ⟨k₂, rfl⟩ := hπ a₂
  exact ⟨⁅k₁, k₂⁆, comm_mem_iInf_fixSubgroup π hker α β hαβ (hA ha₁) (hA ha₂),
    map_commutatorElement _ _ _⟩

end Fix

section Layers

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q] {ι : Type*}

theorem glaPComponent_map_iInf_fixSubgroup (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) {J : Subgroup K}
    (hJ : GLAPComponent p (⨅ i, fixSubgroup (α i)) J) :
    GLAPComponent p (⨅ i, fixSubgroup (β i)) (J.map π) :=
  CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp
    (map_iInf_fixSubgroup_le π hker α β hαβ)
    (normal_map_iInf_fixSubgroup π hker α β hαβ hπ)
    (glaPComponent_map_central hp π (kerCentral_iInf_fixSubgroup π hker α) hJ)

theorem exists_glaPComponent_map_iInf_fixSubgroup (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (α : ι → MulAut K) (β : ι → MulAut Q)
    (hαβ : ∀ i k, π (α i k) = β i (π k)) (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    {A : Subgroup Q} (hA : GLAPComponent p (⨅ i, fixSubgroup (β i)) A) :
    ∃ J : Subgroup K, GLAPComponent p (⨅ i, fixSubgroup (α i)) J ∧ J.map π = A := by
  have hAH : A ≤ ((⨅ i, fixSubgroup (α i))).map π :=
    le_map_iInf_fixSubgroup_of_perfect π hker α β hαβ hπ hA.1 (glaPComponent_perfect hA)
  exact exists_glaPComponent_map_central hp π (kerCentral_iInf_fixSubgroup π hker α)
    (glaPComponent_of_le hp hA hAH (map_iInf_fixSubgroup_le π hker α β hαβ))

theorem map_glaPLayer_iInf_fixSubgroup_eq (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : ι → MulAut K) (β : ι → MulAut Q) (hαβ : ∀ i k, π (α i k) = β i (π k))
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) :
    (GLAPLayer p (⨅ i, fixSubgroup (α i))).map π = GLAPLayer p (⨅ i, fixSubgroup (β i)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hJ' := glaPComponent_map_iInf_fixSubgroup π hker α β hαβ hπ hp hJ
    exact le_sSup hJ'
  · refine sSup_le fun A hA => ?_
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_iInf_fixSubgroup π hker α β hαβ hπ hp hA
    exact Subgroup.map_mono (le_sSup hJ)

end Layers

section Comap

variable {G S : Type} [Group G] [Group S]

theorem iInf_fixSubgroup_comap (ρ : G →* MulAut S) {F : Subgroup (MulAut S)}
    (hF : F ≤ ρ.range) :
    (⨅ b : ↥(F.comap ρ), fixSubgroup (ρ b)) = ⨅ f ∈ F, fixSubgroup f := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun f => le_iInf fun hf => ?_
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (hF hf)
    have hbF : b ∈ F.comap ρ := by rw [Subgroup.mem_comap, hb]; exact hf
    calc (⨅ b : ↥(F.comap ρ), fixSubgroup (ρ b)) ≤
          fixSubgroup (ρ (⟨b, hbF⟩ : ↥(F.comap ρ))) :=
          iInf_le (fun b : ↥(F.comap ρ) => fixSubgroup (ρ b)) ⟨b, hbF⟩
      _ = fixSubgroup f := congrArg fixSubgroup hb
  · refine le_iInf fun b => ?_
    exact iInf₂_le (ρ (b : G)) (Subgroup.mem_comap.1 b.2)

end Comap

end CFSG.HardMathSupport.Solomon.Coordinator

end
