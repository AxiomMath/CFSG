module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGQGroups.Defs
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter CFSG.ABGQGroups

universe u v

section GW

theorem oddCore_eq_pPrimeCore (G : Type*) [Group G] : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem gw_cases
    {G : Type} [Group G] [Finite G] (hD : HasDihedralSylowTwo G)
    (hO : CFSG.oddCore G = ⊥) :
    IsPGroup 2 G ∨ Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        ∃ L : Subgroup G, L.Normal ∧ Odd L.index ∧
          (Nonempty (L ≃* PSL2 F) ∨ Nonempty (L ≃* PGL2 F)) := by
  have hO2 : CFSG.pPrimeCore 2 G = ⊥ := (oddCore_eq_pPrimeCore G) ▸ hO
  let qE : (G ⧸ CFSG.pPrimeCore 2 G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  rcases CFSG.GorensteinWalter.gorensteinWalter G hD with
    ⟨_, hQ⟩ | ⟨_, ⟨e7⟩⟩ | ⟨_, K, hK, L', hL'n, hL'idx, hL'model⟩
  · exact Or.inl (hQ.of_equiv qE)
  · exact Or.inr (Or.inl ⟨qE.symm.trans e7⟩)
  · right
    right
    refine ⟨K, inferInstance, inferInstance, hK, L'.map qE.toMonoidHom,
      hL'n.map _ qE.surjective, ?_, ?_⟩
    · rw [index_map_mulEquiv]
      exact hL'idx
    · let eL : L' ≃* L'.map qE.toMonoidHom := L'.equivMapOfInjective _ qE.injective
      rcases hL'model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact Or.inl ⟨eL.symm.trans e⟩
      · exact Or.inr ⟨eL.symm.trans e⟩

end GW

section Structure

theorem oddCore_eq_bot_of_mulEquiv {A : Type*} {B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.oddCore A = ⊥) : CFSG.oddCore B = ⊥ := by
  rw [oddCore_eq_pPrimeCore] at h ⊢
  rw [← CFSG.pPrimeCore_map_iso 2 e, h, Subgroup.map_bot]

end Structure

end CFSG.QuasiDihedralFusion
