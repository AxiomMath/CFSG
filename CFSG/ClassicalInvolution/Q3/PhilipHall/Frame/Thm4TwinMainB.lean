module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTwoC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinStruct
public import CFSG.ClassicalInvolution.Q3.TL4SepMainB

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

@[expose] def Thm4TwinRes2CD (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    ∀ u v : G, IsUniqueInvolution J u → IsUniqueInvolution L v → TightInO2 u → TightInO2 v →
      v ∉ Subgroup.normalizer (J : Set G) → (r ≤ 3 ∨ (r = 4 ∧ v * u = u * v)) → False

theorem thm4TwinRes2C_of_res2CD {r n : ℕ} (h : Thm4TwinRes2CD r n) : Thm4TwinRes2C r n := by
  intro G _ _ hG J L hm hgen
  obtain ⟨u, hu⟩ := (hm.hyp.hyp.omega1 J hm.memJ).1
  obtain ⟨v, hv⟩ := (hm.hyp.hyp.omega1 L hm.memL).1
  have hnu : ¬ TightInO2 u ∧ ¬ TightInO2 v := by
    by_cases hinu : TightInO2 u <;> by_cases hinv : TightInO2 v
    · exfalso
      by_cases hvJ : v ∈ Subgroup.normalizer (J : Set G)
      · exact hm.false_of_mem_normalizer hu hv hinu hinv hvJ
      · exact h G hG J L hm hgen u v hu hv hinu hinv hvJ
          (hm.hyp.le_four_of_not_mem_normalizer hm.memJ hm.memL hu hv hinu hinv hvJ)
    · exact absurd (hm.false_of_mixed hu hv hinu hinv) id
    · exact absurd (hm.symm.false_of_mixed hv hu hinv hinu) id
    · exact ⟨hinu, hinv⟩
  rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩) z hz hzO
  · exact hnu.1 (TL4.tightInO2_of_conj g (hz.eq (hu.conj g) ▸ hzO))
  · exact hnu.2 (TL4.tightInO2_of_conj g (hz.eq (hv.conj g) ▸ hzO))

@[expose] def Thm4TwinRes2F' (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ L₀ : Subgroup G, CFSG.IsComponent L₀ → L₀.Normal → layer G = L₀ →
      generalizedFitting G = L₀ ⊔ pCore 2 G → pCore 2 G = Subgroup.center G →
      Subgroup.centralizer (L₀ : Set G) = Subgroup.center G →
      (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀) → False

theorem thm4TwinRes2F_of_res2F' {r n : ℕ} (hA : Thm4TwinThmA r) (h : Thm4TwinRes2F' r n) :
    Thm4TwinRes2F r n := by
  intro G _ _ hG J L hm hgen hno L₀ hL₀ hmem
  have hyp := hm.hyp
  exact h G hG J L hm hgen hno L₀ hL₀ (hyp.component_normal hA hgen hno hL₀)
    (hyp.layer_eq_of_inv_mem hA hgen hno hL₀ hmem)
    (hyp.generalizedFitting_eq_of_inv_mem hA hgen hno hL₀ hmem) (hyp.pCore_eq_center hgen hno)
    (hyp.centralizer_eq_center_of_inv_mem hA hgen hno hL₀ hmem) hmem

theorem thm4RTwinBelow_of_res2CD {r n : ℕ} (hA : Thm4TwinThmA r) (h2c : Thm4TwinRes2CD r n)
    (h2f : Thm4TwinRes2F r n) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_residuals hA (thm4TwinRes2C_of_res2CD h2c) h2f

theorem thm4RTwinBelow_of_res2CD_res2F' {r n : ℕ} (hA : Thm4TwinThmA r)
    (h2c : Thm4TwinRes2CD r n) (h2f : Thm4TwinRes2F' r n) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_res2CD hA h2c (thm4TwinRes2F_of_res2F' hA h2f)

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
