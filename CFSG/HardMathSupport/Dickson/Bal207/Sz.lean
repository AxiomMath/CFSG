module

public import CFSG.HardMathSupport.Dickson.Bal207.Rank

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def Bal207SzAut : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsLieQuot K IsSuzuki2Index →
    ∀ α : MulAut K, α ^ 5 = 1 →
      (∀ y : K, y ^ 5 = 1 → α y = y → MulAut.conj y ∈ Subgroup.zpowers α) →
        ∀ T : Subgroup (MulAut K), Nat.Coprime 5 (Nat.card T) →
          α ∈ Subgroup.normalizer (T : Set (MulAut K)) → T = ⊥

theorem bal207SzCyclic_of_aut (h : Bal207SzAut) : Bal207SzCyclic := by
  intro X _ _ _ K B hcomp hSC hBN hK hcyc
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have hBel : IsElemAbelian 5 B := hSC.2.1
  obtain ⟨A, hAB, hAC, hAsup⟩ := rankAux_exists_complement (K := K) hp hBel
  haveI := hcyc A hAB hAC hAsup
  obtain ⟨x, hxA⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp inferInstance
  have hxB : x ∈ B := hAB (hxA ▸ Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hBN hxB
  have hxp : x ^ 5 = 1 := hBel.2 x hxB
  set ψ := K.normalizerMonoidHom with hψdef
  have hψ := rankAux_normalizerMonoidHom_apply K
  have hαp : ψ ⟨x, hxN⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 5 = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [h1, map_one]
  rw [← hxA] at hAsup
  have hfix : ∀ y : ↥K, y ^ 5 = 1 → ψ ⟨x, hxN⟩ y = y →
      MulAut.conj y ∈ Subgroup.zpowers (ψ ⟨x, hxN⟩) :=
    fun y hy hyα => rankAux_conj_mem_zpowers hSC hxN hAsup hy hyα
  intro S hSN hS5 hBS
  set S' : Subgroup ↥(Subgroup.normalizer (K : Set X)) :=
    S.subgroupOf (Subgroup.normalizer (K : Set X)) with hS'
  set T : Subgroup (MulAut ↥K) := S'.map ψ with hT
  have hT5 : Nat.Coprime 5 (Nat.card T) := by
    have h1 : Nat.card T ∣ Nat.card S' := Subgroup.card_map_dvd S' ψ
    have h2 : Nat.card S' = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hS5
  have hxS : x ∈ Subgroup.normalizer (S : Set X) := hBS ⟨hxB, hxN⟩
  have hαT : ψ ⟨x, hxN⟩ ∈ Subgroup.normalizer (T : Set (MulAut ↥K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨x, hxN⟩ * s * (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X)))⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, hS', Subgroup.mem_subgroupOf] at hs ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp hxS _).mp hs
      · simp only [map_mul, map_inv]
    · rintro ⟨s, hs, hst⟩
      refine ⟨(⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X)))⁻¹ * s * ⟨x, hxN⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, hS', Subgroup.mem_subgroupOf] at hs ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hxS) _).mp hs
        simpa using h1
      · simp only [map_mul, map_inv]
        rw [hst]
        group
  have hTbot := h ↥K hcomp.2.2 hK _ hαp hfix T hT5 hαT
  intro s hs
  have hsN := hSN hs
  have h1 : ψ ⟨s, hsN⟩ = 1 := by
    have h2 : ψ ⟨s, hsN⟩ ∈ T := ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hTbot] at h2
    exact h2
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : X)) h1
  simp only [hψdef, hψ, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

end CFSG.HardMathSupport.Dickson.Bal207
