module

public import CFSG.CGT.PushingUpLit.SYMB.FiveSplit
public import CFSG.CGT.PushingUpLit.SYMB.Seven
public import CFSG.CGT.PushingUpLit.SYMB.FiveFamily
public import CFSG.CGT.PushingUpLit.SYMB.FiveBad
public import CFSG.CGT.PushingUpLit.SYMB.FiveSquares

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

@[expose] def SymFiveRigid : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T V : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin 5))
    (ψ : ↥V →* ↥(G6.coreMod 5)) (T' : Set (Equiv.Perm (Fin 5)))
    (S : SymSetting G T V 5 φ ψ T') (E : Subgroup Γ) (h : FiveCase S E) (z : Γ),
    z ∈ E ⊓ Subgroup.centralizer (V : Set Γ) → z ∉ ⁅V, E⁆ → z ^ 2 = 1 →
    (∀ g ∈ G, g * z = z * g) →
    (∀ (e : Γ) (he : e ∈ E), (φ ⟨e, h.join.le he⟩) ^ 2 = 1 → φ ⟨e, h.join.le he⟩ ≠ 1 →
      z⁻¹ * e ^ 2 ∈ ⁅V, E⁆) → False

theorem symCaseTwoFive_of_rigid (hrig : SymFiveRigid) : SymCaseTwoFive := by
  intro Γ _ _ G T V m hm φ ψ T' S hih hno
  obtain rfl : m = 2 := hm
  classical
  have hJ : SymJoin G T V φ ψ (sSup (triBlocks G T φ)) := symJoin_triBlocks S (le_refl 2) hih
  set E : Subgroup Γ := sSup (triBlocks G T φ) with hE
  have hblk : ∀ F ∈ triBlocks G T φ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T :=
    fun F hF => ⟨hF.1, hF.2.1⟩
  have hcase : FiveCase S E :=
    ⟨hJ, symJoin_normal S hJ hno, symJoin_sup_T S hJ hno, blocks_comm_pCore_le S hblk⟩
  have hV : V1Iso S ⁅V, E⁆ := hcase.v1Iso
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hKE : K ≤ E := inf_le_left
  have hKle : K ≤ ⁅V, E⁆ := by
    by_contra hnle
    obtain ⟨y, hyK, hKy, hy2, hsq⟩ := hcase.exists_sq_gen
    have hybad : y ∉ ⁅V, E⁆ := fun hy => hnle (hKy.trans (sup_le
      ((Subgroup.zpowers_le).2 hy) le_rfl))
    obtain ⟨z, hzK, hzV, hz2, hzG, hyz, -⟩ := exists_central_gen hV hcase rfl hyK hKy hy2 hybad
    refine hrig Γ G T V φ ψ T' S E hcase z hzK hzV hz2 hzG ?_
    intro e he he2 he1
    have h1 := hsq e he he2 he1
    have h2 : z⁻¹ * e ^ 2 = (y⁻¹ * z)⁻¹ * (y⁻¹ * e ^ 2) := by group
    rw [h2]
    exact (⁅V, E⁆).mul_mem ((⁅V, E⁆).inv_mem hyz) h1
  have hV₁K : ⁅V, E⁆ ≤ K := hcase.V₁_le_K
  have hKV : K ≤ V := hKle.trans (comm_V_E_le_V S hJ.le)
  have hKnorm : E ≤ Subgroup.normalizer (K : Set Γ) := hJ.le_normalizer_ker S.data.normal
  have hKE' : ⁅K, E⁆ = K := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro k hk e he
      have e' : ⁅k, e⁆ = k * (e * k⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e']
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hKnorm he) k⁻¹).mp (K.inv_mem hk))
    · calc K ≤ ⁅V, E⁆ := hKle
        _ = ⁅⁅V, E⁆, E⁆ := (hV.comm_V₁_E hcase).symm
        _ ≤ ⁅K, E⁆ := Subgroup.commutator_mono hV₁K le_rfl
  exact ⟨E, hJ.isBTBlock (le_refl 2) S hKV hKE', hJ.img_eq_alt⟩

end CFSG.CGT.PushingUpLit.SYMB
