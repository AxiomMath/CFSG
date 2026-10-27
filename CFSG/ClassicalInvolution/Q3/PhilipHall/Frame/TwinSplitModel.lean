module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSplitSp6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSplitO8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4

@[expose] def E4SplitWt (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    ∀ K' ∈ CoreAssembly.conjClass K, IsUniqueInvolution K' s → K' ≠ K →
      ∃ c : M, c ^ 3 = 1 ∧ conjSub c K = K ∧ (∀ y ∈ K', c * y = y * c) ∧
        ∃ k ∈ K, c * k * c⁻¹ ≠ k

@[expose] def E4SplitModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) →
      E4SplitWt M

theorem e4SplitWt_of_model {M G : Type} [Group M] [Group G] (H Kc : Subgroup G)
    (hid : ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) →
      IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hfin : ∀ sc, IsUniqueInvolution Kc sc → ∀ h ∈ H, IsUniqueInvolution (conjSub h Kc) sc →
      conjSub h Kc ≠ Kc → ∃ c ∈ H, c ^ 3 = 1 ∧ conjSub c Kc = Kc ∧
        (∀ y ∈ conjSub h Kc, c * y = y * c) ∧ ∃ k ∈ Kc, c * k * c⁻¹ ≠ k) :
    E4SplitWt M := by
  intro K s hq hinv htw K' hK' hs' hne
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hq hinv htw
  have hs : IsUniqueInvolution Kc (φ s) := hKc ▸ Vtx.isUniqueInvolution_map φ hφ hinv
  obtain ⟨g, rfl⟩ := hK'
  have hgH : φ g ∈ H := hrange ▸ ⟨g, rfl⟩
  have hJt : IsUniqueInvolution (conjSub (φ g) Kc) (φ s) := by
    have := Vtx.isUniqueInvolution_map φ hφ hs'
    rwa [← conjSub_map, hKc] at this
  have hne' : conjSub (φ g) Kc ≠ Kc := by
    intro h
    apply hne
    apply Subgroup.map_injective hφ
    rw [← conjSub_map, hKc]
    exact h
  obtain ⟨c', hc'H, h3, hN, hC, k', hk'Kc, hk'⟩ := hfin (φ s) hs (φ g) hgH hJt hne'
  rw [← hrange] at hc'H
  obtain ⟨c, rfl⟩ := hc'H
  refine ⟨c, ?_, ?_, fun y hy => ?_, ?_⟩
  · apply hφ
    rw [map_pow, h3, map_one]
  · apply Subgroup.map_injective hφ
    rw [← conjSub_map, hKc]
    exact hN
  · apply hφ
    rw [map_mul, map_mul]
    apply hC
    have := Subgroup.mem_map_of_mem φ hy
    rwa [← conjSub_map, hKc] at this
  · rw [← hKc] at hk'Kc
    obtain ⟨k, hk, rfl⟩ := hk'Kc
    refine ⟨k, hk, fun h => hk' ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, h]

theorem e4SplitModel_of_certs :
    E4SplitModel := by
  intro M _ _ hM
  rcases hM with hM | hM
  · obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
    exact e4SplitWt_of_model CFSG.Sporadic.Schreier.Co3.co3X36 E4Sp6.K0
      (fun K s hq hinv htw => TwinThmE.exists_emb_of_ident e
        (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw)
      (fun sc hsc h hh ht hne => E4Sp6.split_fin hsc hh ht hne)
  · obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hM
    exact e4SplitWt_of_model CFSG.EvenSmallLie.OmegaEight.omegaT E4O8.K0
      (fun K s hq hinv htw => TwinThmE.exists_emb_of_ident e
        (fun K s hd => E4O8.ident_omega hd) hq hinv htw)
      (fun sc hsc h hh ht hne => E4O8.split_fin hsc hh ht hne)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin
