module

public import CFSG.GH74.Generic.BProg.B3.S3T5L3Tmpl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphOrth
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Outer

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer

attribute [local instance] conj_range_normal

variable {K : Type} [Group K]

noncomputable def innEquiv (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) :
    K ≃* (MulAut.conj : K →* MulAut K).range :=
  MonoidHom.ofInjective (conj_injective_of hZ)

theorem innEquiv_apply (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) (x : K) :
    ((innEquiv hZ x : (MulAut.conj : K →* MulAut K).range) : MulAut K) = MulAut.conj x :=
  MonoidHom.ofInjective_apply _

theorem conjNormal_innEquiv (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) (α : MulAut K)
    (x : K) : MulAut.conjNormal α (innEquiv hZ x) = innEquiv hZ (α x) := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, innEquiv_apply, innEquiv_apply, aut_mul_conj_mul_inv]

theorem inf_centralizer_inn_eq_bot (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1)
    (X : Subgroup (MulAut K)) :
    X ⊓ centralizer ((MulAut.conj : K →* MulAut K).range : Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff_forall]
  rintro α ⟨-, hα⟩
  ext k
  exact apply_eq_of_commute hZ ((mem_centralizer_iff.1 hα) _ ⟨k, rfl⟩).symm

theorem mem_normalizer_of_conjNormal {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) {X : Subgroup (MulAut K)}
    (hN : ∀ c ∈ H, c * (u : MulAut K) = u * c → c ∈ normalizer (X : Set (MulAut K)))
    (j : (MulAut.conj : K →* MulAut K).range) (hj : MulAut.conjNormal (u : MulAut K) j = j) :
    (j : MulAut K) ∈ normalizer (X : Set (MulAut K)) := by
  refine hN j (hH j.2) ?_
  have h := congrArg Subtype.val hj
  rw [MulAut.conjNormal_apply] at h
  calc (j : MulAut K) * u = (u * j * (u : MulAut K)⁻¹) * u := by rw [h]
    _ = u * j := by group

variable [Finite K]

theorem oddCore_bot_linGraph {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) (e₀ : K ≃* projectiveSL 3 F)
    (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B)
    (hα : MulAut.congr e₀ (u : MulAut K) = conjAut 3 F B * dualAut 3 F) :
    involutionOddCore u = ⊥ := by
  refine involutionOddCore_eq_bot_of_pGroup u fun p hp hp2 X hX hX1 hN => ?_
  have : Fact p.Prime := ⟨hp⟩
  refine Odd87.fl3_graph_false hodd h3 ((innEquiv hZ).symm.trans e₀)
    (MulAut.conjNormal (u : MulAut K)) B hB (fun k => ?_) hp2 hX hX1
    (inf_centralizer_inn_eq_bot hZ X) (mem_normalizer_of_conjNormal hH u hN)
  obtain ⟨x, rfl⟩ := (innEquiv hZ).surjective k
  rw [conjNormal_innEquiv, ← hα]
  simp [MulAut.congr_apply]

theorem oddCore_bot_uni {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (ℓ ^ f) ^ 2)
    (e₀ : K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1)
    {H : Subgroup (MulAut K)} (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H)
    (hu : u * u = 1) (hout : (u : MulAut K) ∉ (MulAut.conj : K →* MulAut K).range) :
    involutionOddCore u = ⊥ := by
  refine involutionOddCore_eq_bot_of_pGroup u fun p hp hp2 X hX hX1 hN => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hu' : (u : MulAut K) * u = 1 := congrArg Subtype.val hu
  refine Odd87.fu3_outer_false hℓ hℓ2 hf h3 hF ((innEquiv hZ).symm.trans e₀)
    (σ := MulAut.conjNormal (u : MulAut K)) (by rw [← map_mul, hu', map_one]) ?_ hp2 hX hX1
    (inf_centralizer_inn_eq_bot hZ X) (mem_normalizer_of_conjNormal hH u hN)
  rintro ⟨s, hs⟩
  obtain ⟨s₀, rfl⟩ := (innEquiv hZ).surjective s
  refine hout ⟨s₀, ?_⟩
  ext x
  have h := hs (innEquiv hZ x)
  rw [conjNormal_innEquiv, ← map_inv, ← map_mul, ← map_mul] at h
  rw [(innEquiv hZ).injective h, MulAut.conj_apply]

end CFSG.GH74.Generic.BProg.B3.S3T5L3
