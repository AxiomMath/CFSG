module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRigid
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeP

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false

section Graph

variable {L : Type} [Field L] (t : TwistTag)

theorem height_permLattice (π : Equiv.Perm (Fin t.tag.rank)) (v : Fin t.tag.rank → ℤ) :
    height (permLattice π v) = height v := by
  unfold height permLattice
  exact Equiv.sum_comp π.symm v

theorem conj_diagramMap_posUnipotent_le :
    (posUnipotent t.tag L).map (MulAut.conj (diagramMap t L)).toMonoidHom ≤ posUnipotent t.tag L ∧
    (posUnipotent t.tag L).map (MulAut.conj (diagramMap t L)⁻¹).toMonoidHom ≤
      posUnipotent t.tag L := by
  constructor
  · refine map_rootSpan_le_of_forall fun γ hγ s => ?_
    obtain ⟨e, he, hP⟩ := diagramMap_conj_pinnedX (K := L) t hγ.1
    show diagramMap t L * pinnedX t.tag L γ s * (diagramMap t L)⁻¹ ∈ _
    rw [hP]
    exact pinnedX_mem_rootSpan (S := {α | IsRoot t.tag α ∧ 0 < height α})
      ⟨hγ.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hγ.2⟩ _
  · refine map_rootSpan_le_of_forall fun γ hγ s => ?_
    have hγ' : IsRoot t.tag (permLattice t.perm.symm γ) :=
      hγ.1.permLattice (cartan_perm_symm (TwistTag.cartan_perm t))
    obtain ⟨e, he, hP⟩ := diagramMap_conj_pinnedX (K := L) t hγ'
    have hinv : permLattice t.perm (permLattice t.perm.symm γ) = γ := by
      funext i
      simp [permLattice]
    rw [hinv] at hP
    show (diagramMap t L)⁻¹ * pinnedX t.tag L γ s * (diagramMap t L)⁻¹⁻¹ ∈ _
    have h2 : (diagramMap t L)⁻¹ * pinnedX t.tag L γ s * (diagramMap t L)⁻¹⁻¹ =
        pinnedX t.tag L (permLattice t.perm.symm γ) (e * s) := by
      have h3 := hP (e * s)
      rw [← mul_assoc, he, one_mul] at h3
      rw [inv_inv]
      calc (diagramMap t L)⁻¹ * pinnedX t.tag L γ s * diagramMap t L =
          (diagramMap t L)⁻¹ * (diagramMap t L * pinnedX t.tag L (permLattice t.perm.symm γ)
            (e * s) * (diagramMap t L)⁻¹) * diagramMap t L := by rw [h3]
        _ = _ := by group
    rw [h2]
    exact pinnedX_mem_rootSpan (S := {α | IsRoot t.tag α ∧ 0 < height α})
      ⟨hγ', by
        have : height (permLattice t.perm.symm γ) = height γ := height_permLattice t _ _
        rw [this]; exact hγ.2⟩ _

end Graph

section Main

variable {L : Type} [Field L] [IsAlgClosed L] (t : TwistTag)

theorem diagramMap_pow_conj_rootDiagUnit' (k : ℕ) (b : Fin t.tag.rank → Lˣ) :
    diagramMap t L ^ k * rootDiagUnit t.tag b * (diagramMap t L ^ k)⁻¹ =
      rootDiagUnit t.tag (fun i => b ((t.perm.symm)^[k] i)) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have h1 : diagramMap t L ^ (k + 1) * rootDiagUnit t.tag b * (diagramMap t L ^ (k + 1))⁻¹ =
        diagramMap t L * (diagramMap t L ^ k * rootDiagUnit t.tag b *
          (diagramMap t L ^ k)⁻¹) * (diagramMap t L)⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]
      group
    rw [h1, ih]
    have h2 := diagramMap_mul_rootDiagUnit (K := L) (t := t)
      (fun i => b ((t.perm.symm)^[k] i))
    calc diagramMap t L * rootDiagUnit t.tag (fun i => b ((t.perm.symm)^[k] i)) *
          (diagramMap t L)⁻¹ =
        rootDiagUnit t.tag (fun i => b ((t.perm.symm)^[k] (t.perm.symm i))) *
          diagramMap t L * (diagramMap t L)⁻¹ := by rw [h2]
      _ = _ := by
        rw [mul_inv_cancel_right]
        rfl

theorem pos_conj_pow (k : ℕ) :
    (∀ y ∈ posUnipotent t.tag L, diagramMap t L ^ k * y * (diagramMap t L ^ k)⁻¹ ∈
      posUnipotent t.tag L) ∧
    (∀ y ∈ posUnipotent t.tag L, (diagramMap t L ^ k)⁻¹ * y * diagramMap t L ^ k ∈
      posUnipotent t.tag L) := by
  obtain ⟨h1, h2⟩ := conj_diagramMap_posUnipotent_le (L := L) t
  have hf : ∀ y ∈ posUnipotent t.tag L, diagramMap t L * y * (diagramMap t L)⁻¹ ∈
      posUnipotent t.tag L := fun y hy => h1 ⟨y, hy, rfl⟩
  have hb : ∀ y ∈ posUnipotent t.tag L, (diagramMap t L)⁻¹ * y * diagramMap t L ∈
      posUnipotent t.tag L := fun y hy => by
    have := h2 ⟨y, hy, rfl⟩
    simpa using this
  induction k with
  | zero => exact ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
  | succ k ih =>
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have e : diagramMap t L ^ (k + 1) * y * (diagramMap t L ^ (k + 1))⁻¹ =
          diagramMap t L * (diagramMap t L ^ k * y * (diagramMap t L ^ k)⁻¹) *
            (diagramMap t L)⁻¹ := by
        rw [pow_succ', _root_.mul_inv_rev]
        group
      rw [e]
      exact hf _ (ih.1 y hy)
    · have e : (diagramMap t L ^ (k + 1))⁻¹ * y * diagramMap t L ^ (k + 1) =
          (diagramMap t L ^ k)⁻¹ * ((diagramMap t L)⁻¹ * y * diagramMap t L) *
            diagramMap t L ^ k := by
        rw [pow_succ, _root_.mul_inv_rev]
        group
      rw [e]
      exact ih.2 _ (hb y hy)

theorem not_centralizes_coset_pow (k : ℕ) (hk : ∃ i, (t.perm.symm)^[k] i ≠ i)
    {c : ModGL t.tag L} (hc : c ∈ adjointGroup t.tag L) :
    ¬ ∀ g ∈ adjointGroup t.tag L, Commute (c * diagramMap t L ^ k) g := by
  intro hcent
  obtain ⟨hTcomm, -, hTnorm, hinf, hHU, -, -, -, -, -, -, hBG⟩ :=
    triangular_borel_structure (τ := t.tag) (R := L)
  have hBadj : borelGroup t.tag L ≤ adjointGroup t.tag L := (hBG L).1
  have hUB : posUnipotent t.tag L ≤ borelGroup t.tag L := le_sup_right
  obtain ⟨hU1, hU2⟩ := pos_conj_pow (L := L) t k
  have hcpos : ∀ y ∈ posUnipotent t.tag L, c * y * c⁻¹ ∈ posUnipotent t.tag L := by
    intro y hy
    have hx := hU2 y hy
    have hcm := (hcent _ (hBadj (hUB hx))).eq
    have : c * y * c⁻¹ = (diagramMap t L ^ k)⁻¹ * y * diagramMap t L ^ k := by
      have h3 : c * diagramMap t L ^ k * ((diagramMap t L ^ k)⁻¹ * y * diagramMap t L ^ k) * (c * diagramMap t L ^ k)⁻¹ = (diagramMap t L ^ k)⁻¹ * y * diagramMap t L ^ k := by
        rw [hcm]; group
      calc c * y * c⁻¹ = c * diagramMap t L ^ k * ((diagramMap t L ^ k)⁻¹ * y * diagramMap t L ^ k) * (c * diagramMap t L ^ k)⁻¹ := by group
        _ = _ := h3
    rw [this]
    exact hx
  have hcneg : ∀ y ∈ posUnipotent t.tag L, c⁻¹ * y * c ∈ posUnipotent t.tag L := by
    intro y hy
    have hx := hU1 y hy
    have hcm := (hcent _ (hBadj (hUB hy))).eq
    have : c⁻¹ * y * c = diagramMap t L ^ k * y * (diagramMap t L ^ k)⁻¹ := by
      have h3 : (c * diagramMap t L ^ k)⁻¹ * y * (c * diagramMap t L ^ k) = y := by
        have := hcm
        calc (c * diagramMap t L ^ k)⁻¹ * y * (c * diagramMap t L ^ k) = (c * diagramMap t L ^ k)⁻¹ * (y * (c * diagramMap t L ^ k)) := by group
          _ = (c * diagramMap t L ^ k)⁻¹ * ((c * diagramMap t L ^ k) * y) := by rw [← this]
          _ = y := by group
      calc c⁻¹ * y * c = diagramMap t L ^ k * ((c * diagramMap t L ^ k)⁻¹ * y * (c * diagramMap t L ^ k)) * (diagramMap t L ^ k)⁻¹ := by group
        _ = _ := by rw [h3]
    rw [this]
    exact hx
  have hcN : c ∈ Subgroup.normalizer (posUnipotent t.tag L : Set (ModGL t.tag L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hcpos h, fun hh => ?_⟩
    have := hcneg _ hh
    simpa [mul_assoc] using this
  have hcB : c ∈ borelGroup t.tag L := by
    rw [← (borel_self_normalizers t.tag L).1]
    exact Subgroup.mem_inf.2 ⟨hc, hcN⟩
  obtain ⟨h, hh, v, hv, hcv⟩ : ∃ h ∈ torusGroup t.tag L, ∃ v ∈ posUnipotent t.tag L, h * v = c := by
    have : c ∈ (torusGroup t.tag L : Set (ModGL t.tag L)) * (posUnipotent t.tag L : Set (ModGL t.tag L)) := by
      rw [← hHU]
      exact hcB
    exact this
  obtain ⟨i₁, hi₁⟩ := hk
  obtain ⟨x, hx0, hx1⟩ : ∃ x : L, x ≠ 0 ∧ x ≠ 1 := by
    classical
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset L)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact ⟨x, hx.1, hx.2⟩
  set u : Lˣ := Units.mk0 x hx0 with hu
  have hu1 : u ≠ 1 := fun h => hx1 (by simpa [hu] using congrArg Units.val h)
  set σ := (t.perm.symm)^[k] with hσ
  let a : Fin t.tag.rank → Lˣ := fun i => if i = σ i₁ then u else 1
  set d := rootDiagUnit t.tag (fun i => a (σ i)) with hd
  have hdT : d ∈ torusGroup t.tag L := rootDiagUnit_mem_torusGroup _
  have haT : rootDiagUnit t.tag a ∈ torusGroup t.tag L := rootDiagUnit_mem_torusGroup _
  have hc1 : c * d * c⁻¹ = rootDiagUnit t.tag a := by
    have hcm := (hcent _ (torusGroup_le_adjointGroup' haT)).eq
    have hPk := diagramMap_pow_conj_rootDiagUnit' (L := L) t k a
    calc c * d * c⁻¹ = c * (diagramMap t L ^ k * rootDiagUnit t.tag a * (diagramMap t L ^ k)⁻¹) * c⁻¹ := by rw [hPk]
      _ = (c * diagramMap t L ^ k) * rootDiagUnit t.tag a * (c * diagramMap t L ^ k)⁻¹ := by group
      _ = rootDiagUnit t.tag a := by rw [hcm]; group
  have hdn : ∀ y ∈ posUnipotent t.tag L, d⁻¹ * y * d ∈ posUnipotent t.tag L := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.1 (hTnorm (inv_mem hdT)) y).1 hy
    simpa using this
  have hw₁ : (d⁻¹ * v * d) * v⁻¹ ∈ posUnipotent t.tag L :=
    mul_mem (hdn v hv) (inv_mem hv)
  have hw₂ : h * ((d⁻¹ * v * d) * v⁻¹) * h⁻¹ ∈ posUnipotent t.tag L :=
    (Subgroup.mem_normalizer_iff.1 (hTnorm hh) _).1 hw₁
  have hhd : h * d = d * h := hTcomm h hh d hdT
  have hc2 : c * d * c⁻¹ = d * (h * ((d⁻¹ * v * d) * v⁻¹) * h⁻¹) := by
    rw [← hcv]
    calc h * v * d * (h * v)⁻¹ = h * (d * ((d⁻¹ * v * d) * v⁻¹)) * h⁻¹ := by group
      _ = (h * d) * ((d⁻¹ * v * d) * v⁻¹) * h⁻¹ := by group
      _ = _ := by rw [hhd]; group
  have hmem : d⁻¹ * rootDiagUnit t.tag a ∈ torusGroup t.tag L ⊓ posUnipotent t.tag L := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hdT) haT, ?_⟩
    have : d⁻¹ * rootDiagUnit t.tag a = h * ((d⁻¹ * v * d) * v⁻¹) * h⁻¹ := by
      rw [← hc1, hc2]
      group
    rw [this]
    exact hw₂
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have heq := rootDiagUnit_injective hmem.symm
  have h3 := congrFun heq i₁
  have h4 : a i₁ = 1 := by simp only [a]; simp [Ne.symm hi₁]
  have h5 : a (σ i₁) = u := by simp [a]
  simp only [h4, h5] at h3
  exact hu1 h3.symm

theorem noTriCosetCentralizes_D4 :
    NoTriCosetCentralizes TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
  intro c hc a ha0 ha3 hcent
  have hk : ∃ i, (TwistTag.D4.perm.symm)^[a] i ≠ i := by
    interval_cases a
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  have hc' : diagramMap TwistTag.D4 L ^ a * c⁻¹ * (diagramMap TwistTag.D4 L ^ a)⁻¹ ∈
      adjointGroup TwistTag.D4.tag L :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.conj_diagramMap_pow_mem_adjointGroup a (inv_mem hc)
  refine not_centralizes_coset_pow (L := L) TwistTag.D4 a hk hc' fun g hg => ?_
  have h1 := (hcent g hg).inv_left
  have e : (c * (diagramMap TwistTag.D4 L)⁻¹ ^ a)⁻¹ =
      diagramMap TwistTag.D4 L ^ a * c⁻¹ := by
    rw [mul_inv_rev, inv_pow, inv_inv]
  rw [e] at h1
  have e2 : diagramMap TwistTag.D4 L ^ a * c⁻¹ =
      (diagramMap TwistTag.D4 L ^ a * c⁻¹ * (diagramMap TwistTag.D4 L ^ a)⁻¹) *
        diagramMap TwistTag.D4 L ^ a := by group
  rw [← e2]
  exact h1

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
