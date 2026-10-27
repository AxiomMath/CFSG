module

public import CFSG.LieType.Ree.LargeReeRootInvolution
public import CFSG.LieType.Ree.FixedBruhatDecomposition

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

@[expose] def largeReeSigma (a : ℕ) {K : Type*} [CommRing K] (c : K) : K :=
  c ^ (2 * 2 ^ a)

@[expose] def largeReeCoord
    (a : ℕ) (K : Type*) [CommRing K] (t v : K) :
    (Module.End K (RootModule Tag.F4 K))ˣ :=
  largeReeP K t (largeReeSigma a t) v (largeReeSigma a v + t ^ 2 * largeReeSigma a t)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K] [CharP K F4.prime] in
theorem largeReeP_mem_adjointGroup
    (A B C D : K) : largeReeP K A B C D ∈ adjointGroup F4.tag K :=
  mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ A) (pinnedX_mem_adjointGroup _ B))
    (pinnedX_mem_adjointGroup _ C)) (pinnedX_mem_adjointGroup _ D)

omit [Finite K] in
theorem largeReeP_injective
    {A B C D A' B' C' D' : K}
    (h : largeReeP K A B C D = largeReeP K A' B' C' D') : A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have h2 := F4_two_eq_zero (K := K)
  have hv := (bijOn_largeReeP h2).2.1 (Set.mem_univ ![A, B, C, D])
    (Set.mem_univ ![A', B', C', D']) h
  exact ⟨congrFun hv 0, congrFun hv 1, congrFun hv 2, congrFun hv 3⟩

omit [Finite K] [CharP K F4.prime] in
theorem F4_fixedOrbitRoots_one :
    F4.fixedOrbitRoots ⟨1, by decide⟩ = parabolicPosRoots Tag.F4 largeReeBlock := by
  have h : F4.fixedOrbitSet ⟨1, by decide⟩ = largeReeBlock := by
    ext i
    rw [mem_fixedOrbitSet]
    change _ ↔ i.val = 1 ∨ i.val = 2
    revert i
    decide
  rw [fixedOrbitRoots, h]
  rfl

theorem finiteReeAut_largeReeP
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (A B C D : K) :
    ((F4.finiteReeAut K a ⟨largeReeP K A B C D, largeReeP_mem_adjointGroup A B C D⟩ :
        adjointGroup F4.tag K) : ModGL F4.tag K) =
      largeReeP K (B ^ 2 ^ a) (largeReeSigma a A) (D ^ 2 ^ a + largeReeSigma a A * B ^ 2 ^ a)
        (largeReeSigma a C + largeReeSigma a A * (B ^ 2 ^ a) ^ 2) := by
  have h2 := F4_two_eq_zero (K := K)
  obtain ⟨ρ, σ, hρ, hσ, -, -, -, -, -, hR, -⟩ := large_Ree_root_parameter_involution a K hK
  have e : (⟨largeReeP K A B C D, largeReeP_mem_adjointGroup A B C D⟩ : adjointGroup F4.tag K) =
      ⟨largeReeX K 0 A, pinnedX_mem_adjointGroup _ A⟩ *
        ⟨largeReeX K 1 B, pinnedX_mem_adjointGroup _ B⟩ *
        ⟨largeReeX K 2 C, pinnedX_mem_adjointGroup _ C⟩ *
        ⟨largeReeX K 3 D, pinnedX_mem_adjointGroup _ D⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, (hR A).1, (hR B).2.1, (hR C).2.2.1, (hR D).2.2.2]
  have p1 : largeReeX K 1 (σ A) = largeReeP K 0 (σ A) 0 0 := by
    simp [largeReeP, largeReeX_zero]
  have p0 : largeReeX K 0 (ρ B) = largeReeP K (ρ B) 0 0 0 := by
    simp [largeReeP, largeReeX_zero]
  have p3 : largeReeX K 3 (σ C) = largeReeP K 0 0 0 (σ C) := by
    simp [largeReeP, largeReeX_zero]
  have p2 : largeReeX K 2 (ρ D) = largeReeP K 0 0 (ρ D) 0 := by
    simp [largeReeP, largeReeX_zero]
  have key : largeReeX K 1 (σ A) * largeReeX K 0 (ρ B) * largeReeX K 3 (σ C) *
      largeReeX K 2 (ρ D) =
        largeReeP K (B ^ 2 ^ a) (largeReeSigma a A) (D ^ 2 ^ a + largeReeSigma a A * B ^ 2 ^ a)
          (largeReeSigma a C + largeReeSigma a A * (B ^ 2 ^ a) ^ 2) := by
    rw [p1, p0, p3, p2, largeReeP_mul h2, largeReeP_mul h2, largeReeP_mul h2]
    simp only [hρ, hσ, largeReeSigma]
    congr 1 <;> ring
  exact key

theorem finiteReeAut_largeReeCoord
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (t v : K) :
    ((F4.finiteReeAut K a ⟨largeReeCoord a K t v, largeReeP_mem_adjointGroup _ _ _ _⟩ :
        adjointGroup F4.tag K) : ModGL F4.tag K) = largeReeCoord a K t v := by
  have h2 := F4_two_eq_zero (K := K)
  obtain ⟨ρ, σ, hρ, hσ, -, hσρ, -, -⟩ := large_Ree_field_powers a K hK
  have hs : ∀ c, largeReeSigma a c = σ c := fun c => (hσ c).symm
  have hr : ∀ c : K, c ^ 2 ^ a = ρ c := fun c => (hρ c).symm
  have hρσ : ∀ c, ρ (σ c) = c := fun c => congrArg (fun e : K ≃+* K => e c) hσρ
  have hρsq : ∀ c, ρ c ^ 2 = σ c := fun c => by rw [hρ, hσ, ← pow_mul, mul_comm]
  have key := finiteReeAut_largeReeP (a := a) hK t (largeReeSigma a t) v
    (largeReeSigma a v + t ^ 2 * largeReeSigma a t)
  refine key.trans ?_
  simp only [largeReeCoord, hs, hr, hρσ, map_add, map_mul, map_pow, hρsq]
  congr 1
  · linear_combination σ t * t * h2
  · ring

theorem largeReeCoord_mul
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (t v s w : K) :
    largeReeCoord a K t v * largeReeCoord a K s w =
      largeReeCoord a K (t + s) (v + w + largeReeSigma a t * s) := by
  have h2 := F4_two_eq_zero (K := K)
  obtain ⟨ρ, σ, hρ, hσ, -, -, hσσ, -⟩ := large_Ree_field_powers a K hK
  have hs : ∀ c, largeReeSigma a c = σ c := fun c => (hσ c).symm
  simp only [largeReeCoord, hs]
  rw [largeReeP_mul h2]
  simp only [map_add, map_mul, hσσ]
  congr 1
  linear_combination (-(t ^ 2 * σ s + t * s * σ t + t * s * σ s)) * h2

theorem bijOn_largeReeCoord
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × K => largeReeCoord a K p.1 p.2) Set.univ
      (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) := by
  have h2 := F4_two_eq_zero (K := K)
  refine ⟨fun p _ => ?_, fun p _ p' _ h => ?_, fun g hg => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨?_, mem_reeGamma_of_fixed (largeReeP_mem_adjointGroup _ _ _ _)
      (finiteReeAut_largeReeCoord hK p.1 p.2)⟩
    rw [F4_fixedOrbitRoots_one]
    exact largeReeP_mem_rootSpan _ _ _ _
  · obtain ⟨h1, -, h3, -⟩ := largeReeP_injective h
    exact Prod.ext h1 h3
  · obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    rw [F4_fixedOrbitRoots_one] at hgU
    obtain ⟨v, -, rfl⟩ := (bijOn_largeReeP h2).2.2 hgU
    have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (largeReeP_mem_adjointGroup _ _ _ _)
    rw [finiteReeAut_largeReeP hK] at hF
    obtain ⟨e1, e2, -, e4⟩ := largeReeP_injective hF
    rw [e1, e2] at e4
    refine ⟨(v 0, v 2), Set.mem_univ _, ?_⟩
    change largeReeP K (v 0) (largeReeSigma a (v 0)) (v 2)
        (largeReeSigma a (v 2) + v 0 ^ 2 * largeReeSigma a (v 0)) =
      largeReeP K (v 0) (v 1) (v 2) (v 3)
    rw [e2, ← e4]
    ring_nf

theorem large_Ree_B2_fixed_coordinates
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × K => largeReeCoord a K p.1 p.2) Set.univ
      (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ : Set (ModGL F4.tag K)) ∧
    ∀ t v s w : K, largeReeCoord a K t v * largeReeCoord a K s w =
      largeReeCoord a K (t + s) (v + w + largeReeSigma a t * s) :=
  ⟨bijOn_largeReeCoord hK, largeReeCoord_mul hK⟩

end ReeTag

end CFSG.LieType.Ree
