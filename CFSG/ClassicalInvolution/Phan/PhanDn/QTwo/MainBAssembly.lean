module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.MainB
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Model
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.WeakFamily
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.A3Mark
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal
public import CFSG.LieType.Steinberg.Classical.SpinFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.LieType.Universal.Spin in
@[expose] def QTwoSpinModelsD : Prop :=
  (∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → ∀ m : ℕ, 4 ≤ m → Even m →
      Nonempty (QTwoModelD K m ↥(spinGroup (quadPlus m (GaloisField 2 1))))) ∧
    (∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → ∀ m : ℕ, 4 ≤ m → Odd m →
      ∀ b c : GaloisField 2 1, (∀ s, s ^ 2 + b * s + c ≠ 0) →
      Nonempty (QTwoModelD K m ↥(spinGroup (quadMinus m (GaloisField 2 1) b c))))

private theorem iSup_theta_range_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {G : Type} [Group G] {H : Subgroup G} {U : Fin m → Subgroup G}
    {W : Fin m → Fin m → Subgroup G} (hsys : QTwoWeakPhanSystemD K m H U W)
    (hm : 4 ≤ m) (F : QTwoPhanFamily K (CFSG.StandardType.ggCoxeterMatrixD m) G)
    (hFθ : ∀ i j, CFSG.StandardType.ggCoxeterMatrixD m i j = 3 → (F.θ i j).range = W i j) :
    (⨆ (i) (j) (_ : CFSG.StandardType.ggCoxeterMatrixD m i j = 3), (F.θ i j).range) = H := by
  rw [← hsys.iSup_three (ggCoxeterMatrixD_exists_three hm)]
  exact iSup_congr fun i => iSup_congr fun j => iSup_congr fun h3 => hFθ i j h3

theorem ghnsMainBQTwo_of_spinModels (hS : QTwoSpinModelsD) : GHNSMainBQTwo := by
  intro K _ _ _ m hm G _ H U W hsys
  have hK4 : Nat.card K = 4 := hsys.card_four
  obtain ⟨F, -, hFθ⟩ := QTwoWeakPhanSystemD.exists_family (K := K) qTwoA3Mark_holds hm hsys
  constructor
  · intro he
    obtain ⟨d⟩ := hS.1 K hK4 m hm he
    have hU := QTwoModelD.isUniversal hK4 hm d
    obtain ⟨ψ, -, hψθ⟩ := hU.1 G F
    refine ⟨ψ, ?_⟩
    rw [QTwoPhanFamily.range_eq hU.2 hψθ]
    exact iSup_theta_range_eq hsys hm F hFθ
  · intro ho b c hirr
    obtain ⟨d⟩ := hS.2 K hK4 m hm ho b c hirr
    have hU := QTwoModelD.isUniversal hK4 hm d
    obtain ⟨ψ, -, hψθ⟩ := hU.1 G F
    refine ⟨ψ, ?_⟩
    rw [QTwoPhanFamily.range_eq hU.2 hψθ]
    exact iSup_theta_range_eq hsys hm F hFθ

end CFSG.ClassicalInvolution.PhanDn.QTwo
