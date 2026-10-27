module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinMainB

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

@[expose] def HasTwin (Δ : Set (Subgroup G)) : Prop :=
  ∃ K ∈ Δ, ∃ K' ∈ twinSet Δ K, K' ≠ K

omit [Finite G] in
theorem TwinT4Hyp.toT4Hyp_of_noTwin (h : TwinT4Hyp r G Δ) (hno : ¬ HasTwin Δ) :
    TL4.T4Hyp r G Δ := by
  have hsing : ∀ K ∈ Δ, ∀ K' ∈ twinSet Δ K, K' = K := fun K hK K' hK' => by
    by_contra hne
    exact hno ⟨K, hK, K', hK', hne⟩
  refine ⟨h.hyp, h.twoGroup, h.quat, ?_, ?_, h.aEmpty, h.odd⟩
  · intro J hJ u hu c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hcu : c * u * c⁻¹ = u := by rw [hc, mul_inv_cancel_right]
    have hJc : conjSub c J ∈ twinSet Δ J := by
      refine ⟨h.hyp.conjInvariant c J hJ, u, hu, ?_⟩
      have := hu.conj c
      rwa [hcu] at this
    exact mem_normalizer_of_conjSub_eq (hsing J hJ _ hJc)
  · intro J hJ J' hJ' u hu hu'
    exact (hsing J hJ J' ⟨hJ', u, hu, hu'⟩).symm

theorem TwinT4Min.hasTwin {n : ℕ} (ht : TL4.Thm4RBelow r n) (hG : Nat.card G < n) {J L : Subgroup G}
    (hm : TwinT4Min r G Δ J L) : HasTwin Δ := by
  by_contra hno
  exact hm.notComm (ht G hG Δ (hm.hyp.toT4Hyp_of_noTwin hno) J hm.memJ L hm.memL hm.notConj)

@[expose] def Thm4TwinRes2CDTw (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    HasTwin (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ u v : G, IsUniqueInvolution J u → IsUniqueInvolution L v → TightInO2 u → TightInO2 v →
      v ∉ Subgroup.normalizer (J : Set G) → (r ≤ 3 ∨ (r = 4 ∧ v * u = u * v)) → False

@[expose] def Thm4TwinRes2F'Tw (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    HasTwin (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ L₀ : Subgroup G, CFSG.IsComponent L₀ → L₀.Normal → layer G = L₀ →
      generalizedFitting G = L₀ ⊔ pCore 2 G → pCore 2 G = Subgroup.center G →
      Subgroup.centralizer (L₀ : Set G) = Subgroup.center G →
      (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀) → False

theorem thm4TwinRes2CD_of_tight {n : ℕ} (ht : TL4.Thm4RBelow r n) (h : Thm4TwinRes2CDTw r n) :
    Thm4TwinRes2CD r n :=
  fun G _ _ hG J L hm hgen => h G hG J L hm hgen (hm.hasTwin ht hG)

theorem thm4TwinRes2F'_of_tight {n : ℕ} (ht : TL4.Thm4RBelow r n) (h : Thm4TwinRes2F'Tw r n) :
    Thm4TwinRes2F' r n :=
  fun G _ _ hG J L hm hgen => h G hG J L hm hgen (hm.hasTwin ht hG)

theorem thm4RTwinBelow_of_tight {r n : ℕ} (hA : Thm4TwinThmA r) (ht : TL4.Thm4RBelow r n)
    (h2c : Thm4TwinRes2CDTw r n) (h2f : Thm4TwinRes2F'Tw r n) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_res2CD_res2F' hA (thm4TwinRes2CD_of_tight ht h2c)
    (thm4TwinRes2F'_of_tight ht h2f)

theorem thm4RTwinBelow_three_of_tight {n : ℕ} (ht : TL4.Thm4RBelow 3 n)
    (h2c : Thm4TwinRes2CDTw 3 n) (h2f : Thm4TwinRes2F'Tw 3 n) : Thm4RTwinBelow 3 n :=
  thm4RTwinBelow_of_tight thm4TwinThmA_three ht h2c h2f

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
