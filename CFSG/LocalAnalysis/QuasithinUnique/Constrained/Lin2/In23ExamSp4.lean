module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique.Lin2.Exam

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticTwo
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X7a

section TypeKernel

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem typeKernel_map_point {γ : MulAut (StatedProj (StatedSp 2 F))} (hγ : γ ∈ typeKernel F)
    {M : Subgroup (StatedProj (StatedSp 2 F))} (hM : M ∈ pointParabolics F) :
    M.map γ.toMonoidHom ∈ pointParabolics F := by
  rw [mem_typeKernel] at hγ
  rw [← hγ]
  exact ⟨M, hM, rfl⟩

theorem typeKernel_map_plane {γ : MulAut (StatedProj (StatedSp 2 F))} (hγ : γ ∈ typeKernel F)
    {M : Subgroup (StatedProj (StatedSp 2 F))} (hM : M ∈ planeParabolics F) :
    M.map γ.toMonoidHom ∈ planeParabolics F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hdisj, hXne, -⟩ :=
    extremal_parabolics (K := F) 2 (rfl : Nat.card F = Nat.card F)
  obtain ⟨-, -, hcase⟩ := (type_kernel (K := F) 2).1 γ
  rcases hcase with ⟨-, hY⟩ | ⟨hXY, -⟩
  · rw [← hY]
    exact ⟨M, hM, rfl⟩
  · exfalso
    obtain ⟨M₀, hM₀⟩ := hXne
    have h1 : M₀.map γ.toMonoidHom ∈ pointParabolics F := typeKernel_map_point hγ hM₀
    have h2 : M₀.map γ.toMonoidHom ∈ planeParabolics F := by
      rw [← hXY]
      exact ⟨M₀, hM₀, rfl⟩
    exact Set.disjoint_left.mp hdisj h1 h2

end TypeKernel

section Swap

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exam_sp4_swap (hF2 : ∃ k : ℕ, Nat.card F = 2 ^ k)
    (φ : X ≃* StatedProj (StatedSp 2 F)) {R B B' : Subgroup X}
    (hR : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤) (hRB : R ≤ B) (hRB' : R ≤ B')
    (hBp : ⁅B, B⁆ = B) (hBp' : ⁅B', B'⁆ = B') (hBns : ¬ Group.IsSolvable ↥B)
    (hBns' : ¬ Group.IsSolvable ↥B') (hBtop : B ≠ ⊤) (hBtop' : B' ≠ ⊤) (hne : B ≠ B') :
    B ⊔ B' = ⊤ ∧
      ∀ β : MulAut X, B.map β.toMonoidHom = B' → MulAut.congr φ β ∉ typeKernel F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_projUnipotent (K := F) 2 (r := 2) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (SymplecticFlag.projUnipotent 2 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨ψ, -, hres⟩ := (symplectic_two_residualOvergroupsAt hF2).exists_iso_of_isSylow φ hU₀ hR
  set Pm : Fin 2 → Subgroup (StatedProj (StatedSp 2 F)) :=
    fun j => projStabilizer 2 F (flag 2 F ((j : ℕ) + 1)) with hPm
  change ResidualOvergroupsAt X R (fun j => (Pm j).map ψ.symm.toMonoidHom) at hres
  obtain ⟨-, hRP, hmax, -, hC2, -⟩ := hres
  set Pj : Fin 2 → Subgroup X := fun j => (Pm j).map ψ.symm.toMonoidHom with hPj
  have hdInf : ∀ {M : Subgroup X}, ⁅M, M⁆ = M → dInf M = M := fun {M} hM =>
    le_antisymm (dInf_le M) (le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr hM) le_rfl)
  obtain ⟨jB, hjB, hdB⟩ := hC2 B hRB hBtop hBns
  obtain ⟨jB', hjB', hdB'⟩ := hC2 B' hRB' hBtop' hBns'
  have hjne : jB ≠ jB' := by
    intro h
    apply hne
    calc B = dInf B := (hdInf hBp).symm
      _ = dInf (Pj jB) := hdB
      _ = dInf (Pj jB') := by rw [h]
      _ = dInf B' := hdB'.symm
      _ = B' := hdInf hBp'
  have hgen : B ⊔ B' = ⊤ := by
    by_contra hM
    have hRM : R ≤ B ⊔ B' := hRB.trans le_sup_left
    have hMns : ¬ Group.IsSolvable ↥(B ⊔ B') := fun hs =>
      hBns (Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (le_sup_left : B ≤ B ⊔ B')))
    obtain ⟨j, hj, -⟩ := hC2 (B ⊔ B') hRM hM hMns
    have h1 : j = jB := (hjB j).1 (le_sup_left.trans ((hj j).2 rfl))
    have h2 : j = jB' := (hjB' j).1 (le_sup_right.trans ((hj j).2 rfl))
    exact hjne (h1.symm.trans h2)
  refine ⟨hgen, fun β hβ hker => ?_⟩
  set γ : MulAut (StatedProj (StatedSp 2 F)) := MulAut.congr ψ β with hγ
  have hγK : γ ∈ typeKernel F := by
    have hnorm := (type_kernel (K := F) 2).2.1
    have h1 := hnorm.conj_mem _ hker (φ.symm.trans ψ)
    have heq : (φ.symm.trans ψ) * MulAut.congr φ β * (φ.symm.trans ψ)⁻¹ = γ := by
      ext y
      simp [hγ, MulAut.congr_apply]
    rwa [heq] at h1
  have hP0pt : Pm 0 ∈ pointParabolics F := ⟨flag 2 F 1, finrank_flag (by norm_num), rfl⟩
  have hP1pl : Pm 1 ∈ planeParabolics F :=
    ⟨flag 2 F 2, isCompleteIsotropicFlag_flag.2.2 2 (by norm_num), finrank_flag (by norm_num), rfl⟩
  have hdisj := (extremal_parabolics (K := F) 2 (rfl : Nat.card F = Nat.card F)).2.2.1
  have hPjB : Pj jB ⋖ ⊤ := (hmax (Pj jB) (hRP jB)).2 ⟨jB, rfl⟩
  have hcov : (Pj jB).map β.toMonoidHom ⋖ ⊤ := by
    have := (apply_covBy_apply_iff (MulEquiv.mapSubgroup β)).2 hPjB
    rwa [show (MulEquiv.mapSubgroup β) ⊤ = ⊤ from
      Subgroup.map_top_of_surjective _ β.surjective] at this
  have hB'le : B' ≤ (Pj jB).map β.toMonoidHom := by
    rw [← hβ]
    exact Subgroup.map_mono ((hjB jB).2 rfl)
  have hRPβ : R ≤ (Pj jB).map β.toMonoidHom := hRB'.trans hB'le
  obtain ⟨k, hk⟩ := (hmax _ hRPβ).1 hcov
  have hmapψ : ∀ M : Subgroup (StatedProj (StatedSp 2 F)),
      (M.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = M := fun M => by
    rw [Subgroup.map_map]
    have : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id _ := by
      ext y; simp
    rw [this, Subgroup.map_id]
  have hQ : (Pm jB).map γ.toMonoidHom = Pm k := by
    have h1 : ((Pj jB).map β.toMonoidHom).map ψ.toMonoidHom = (Pm jB).map γ.toMonoidHom := by
      rw [hPj]
      simp only [Subgroup.map_map]
      congr 1
    rw [← h1, hk, hPj]
    exact hmapψ (Pm k)
  have hkj : k = jB := by
    by_contra hkne
    have hjk : jB.val ≠ k.val := fun h => hkne (Fin.ext h).symm
    have hjb := jB.isLt
    have hkl := k.isLt
    have hcases : (jB.val = 0 ∧ k.val = 1) ∨ (jB.val = 1 ∧ k.val = 0) := by omega
    rcases hcases with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hjB0 : jB = 0 := Fin.ext h0
      have hk1 : k = 1 := Fin.ext h1
      subst hjB0
      subst hk1
      have hpt : (Pm 0).map γ.toMonoidHom ∈ pointParabolics F := typeKernel_map_point hγK hP0pt
      rw [hQ] at hpt
      exact Set.disjoint_left.mp hdisj hpt hP1pl
    · have hjB1 : jB = 1 := Fin.ext h1
      have hk0 : k = 0 := Fin.ext h0
      subst hjB1
      subst hk0
      have hpl : (Pm 1).map γ.toMonoidHom ∈ planeParabolics F := typeKernel_map_plane hγK hP1pl
      rw [hQ] at hpl
      exact Set.disjoint_left.mp hdisj hP0pt hpl
  subst hkj
  have hB'P : B' ≤ Pj k := by
    rw [← hk]
    exact hB'le
  exact hjne ((hjB' k).1 hB'P)

end Swap

end CFSG.QuasithinUnique.Lin2.Exam
