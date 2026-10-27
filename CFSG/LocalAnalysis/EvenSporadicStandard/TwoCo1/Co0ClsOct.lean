module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.B.TwoA.Census

namespace Co0Cls

@[expose] def octStab : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∀ i, (σ i : ℕ) < 8 ↔ (i : ℕ) < 8}
  one_mem' _ := Iff.rfl
  mul_mem' {σ τ} hσ hτ i := by
    rw [Equiv.Perm.mul_apply, hσ, hτ]
  inv_mem' {σ} hσ i := by
    simpa using (hσ (σ⁻¹ i)).symm

private theorem sylowGenArr_octStab :
    ∀ (k : Fin 10) (i : Fin 24), (sylowGenArr.getD k #[])[(i : ℕ)]! < 8 ↔ (i : ℕ) < 8 := by
  decide

theorem sylowGen_mem_octStab (k : Fin 10) :
    sylowGen k ∈ octStab := by
  have hk : (k : ℕ) < sylowGenArr.length := by simp [sylowGenArr]
  have hp : PermArr (sylowGenArr.getD k #[]) = true :=
    sylowGenArr_perm _ (getD_mem_of_lt hk _)
  intro i
  rw [sylowGen, decode_apply hp]
  exact sylowGenArr_octStab k i

theorem sylowSub_le_octStab : sylowSub ≤ octStab :=
  (Subgroup.closure_le octStab).2 (by
    rintro _ ⟨k, rfl⟩
    exact sylowGen_mem_octStab k)

private theorem bvec_oct (j : Fin 24) : bvec 24 255 j = if (j : ℕ) < 8 then 1 else 0 := by
  revert j
  decide

theorem permWord_oct₁_of_mem_octStab {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ octStab) :
    permWord σ (oct₁ : Fin 24 → ZMod 2) = oct₁ := by
  funext i
  show bvec 24 255 (σ⁻¹ i) = bvec 24 255 i
  rw [bvec_oct, bvec_oct, if_congr (octStab.inv_mem hσ i) rfl rfl]

theorem permC_sylowP_oct₁
    {p : AutPerm} (hp : p ∈ (sylowP : Subgroup AutPerm)) : permC p oct₁ = oct₁ := by
  rw [coe_sylowP, Subgroup.mem_subgroupOf] at hp
  exact Subtype.ext (permWord_oct₁_of_mem_octStab (sylowSub_le_octStab hp))

theorem monoSub_sylowP_le :
    monoSub (sylowP : Subgroup AutPerm) ≤ Subgroup.centralizer {gO oct₁} := by
  rintro _ ⟨a, p, hp, rfl⟩
  exact (mul_PO_mem_centralizer_gO_iff a p oct₁).2 (permC_sylowP_oct₁ hp)

theorem two_pow_dvd_card_centralizer_oct :
    2 ^ 22 ∣ Nat.card (Subgroup.centralizer {gO oct₁}) := by
  have h1 := Subgroup.card_dvd_of_le monoSub_sylowP_le
  rw [card_monoSub, Sylow.card_eq_multiplicity, factorization_card_AutPerm] at h1
  simpa [← pow_add] using h1

end Co0Cls

end CFSG.EvenSporadicStandard.TwoCo1
