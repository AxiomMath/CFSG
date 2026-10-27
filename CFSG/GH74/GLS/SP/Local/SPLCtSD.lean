module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

namespace SylowL2

theorem exists_sylow_eq {I : Type} [Group I] [Finite I] (T₁ : Subgroup I) (hT₁ : IsPGroup 2 T₁)
    (hmax : ∀ P : Subgroup I, IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    ∃ T : Sylow 2 I, (T : Subgroup I) = T₁ := by
  obtain ⟨T, hT⟩ := hT₁.exists_le_sylow
  exact ⟨T, hmax _ T.isPGroup' hT⟩

theorem conjNormal_top_injective {I : Type} [Group I] {F : Type} [Field F] [Finite F]
    (e : ↥(⊤ : Subgroup I) ≃* IVK.L2 F) :
    Function.Injective (MulAut.conjNormal : I →* MulAut ↥(⊤ : Subgroup I)) := by
  intro x y hxy
  obtain ⟨kx, rfl⟩ : ∃ k : ↥(⊤ : Subgroup I), (k : I) = x := ⟨⟨x, trivial⟩, rfl⟩
  obtain ⟨ky, rfl⟩ : ∃ k : ↥(⊤ : Subgroup I), (k : I) = y := ⟨⟨y, trivial⟩, rfl⟩
  rw [MulAut.conjNormal_val, MulAut.conjNormal_val] at hxy
  exact congrArg Subtype.val (IVK.conj_injective_of_L2 e hxy)

end SylowL2

theorem L2_sylow_dihedral {I : Type} [Group I] [Finite I] {q : ℕ}
    (hI : CFSG.GH74.GLS.IVK.IsL2 I (fun r => r = q)) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (T₁ : Subgroup I) (hT₁ : IsPGroup 2 T₁) (hmax : ∀ P : Subgroup I, IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    ∃ m : ℕ, CFSG.GH74.GLS.IVK.IsDihedralOrder ↥T₁ m := by
  obtain ⟨F₀, _, _, hq, ⟨e⟩⟩ := hI
  have hq' : Nat.card F₀ = q := hq
  have hL : IVK.L2Field F₀ := ⟨hq' ▸ hqodd, by omega⟩
  obtain ⟨T, hT⟩ := SylowL2.exists_sylow_eq T₁ hT₁ hmax
  have eK : ↥(⊤ : Subgroup I) ≃* IVK.L2 F₀ := Subgroup.topEquiv.trans e
  obtain ⟨e', N, -, hN⟩ := IVK.ivk_1_2_general F₀ hL I ⊤ ⟨eK⟩ T
  obtain ⟨n, -, k, hk, hk2, ⟨d⟩⟩ := IVK.ivk_1_2c F₀ hL ↥(⊤ : Subgroup I) e' N
  have hmap : T₁.map (MulAut.conjNormal : I →* MulAut ↥(⊤ : Subgroup I)) = N.P := by
    rw [← hT, ← hN, inf_top_eq]
  let φ : ↥T₁ ≃* ↥N.P :=
    (Subgroup.equivMapOfInjective T₁ _ (SylowL2.conjNormal_top_injective eK)).trans
      (MulEquiv.subgroupCongr hmap)
  exact ⟨2 ^ n, k, hk, hk2, ⟨φ.trans d⟩⟩

end CFSG.GH74.GLS.SP.Local
