module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf19Fuse
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf16Fused
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf21Vertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

section Seven

section Gen

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {a₁ a₂ a₃ a₄ : Y}

theorem hyp51At_fusedT_of_cent (hP : PerpHypS n Y R S t)
    (F : StarFrame (CoreAssembly.conjClass (tightCore R)) t K K' K₃ K₄ a₁ a₂ a₃ a₄) {y j : Y}
    (hy : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄) (hyc : y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y))
    (hj₁ : j * a₁ * j⁻¹ = a₁⁻¹) (hj₂ : j * a₂ * j⁻¹ = a₂) (hj₃ : j * a₃ * j⁻¹ = a₃)
    (hj₄ : j * a₄ * j⁻¹ = a₄) :
    Hyp51At (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) (a₁ * a₂ * t * (a₃ * a₄)) := by
  have hpB : a₁ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hqB : a₃ * a₄ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hjt : j * t * j⁻¹ = t := by
    have e : j * t * j⁻¹ = (j * a₂ * j⁻¹) * (j * a₂ * j⁻¹) := by rw [← F.sq₂]; group
    rw [e, hj₂, F.sq₂]
  have hy' : (j * y * j⁻¹) * t * (j * y * j⁻¹)⁻¹ = a₁⁻¹ * a₂ * a₃ * a₄ := by
    have e : (j * y * j⁻¹) * t * (j * y * j⁻¹)⁻¹ = j * (y * (j⁻¹ * t * j) * y⁻¹) * j⁻¹ := by group
    have hjt' : j⁻¹ * t * j = t := by
      have := congrArg (fun x => j⁻¹ * x * j) hjt
      simpa [mul_assoc] using this.symm
    rw [e, hjt', hy]
    calc j * (a₁ * a₂ * a₃ * a₄) * j⁻¹ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) * (j * a₃ * j⁻¹) * (j * a₄ * j⁻¹) := by
          group
      _ = _ := by rw [hj₁, hj₂, hj₃, hj₄]
  have hyc' : j * y * j⁻¹ ∈ Subgroup.centralizer ({a₁⁻¹ * a₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    have hp : a₁⁻¹ * a₂ = j * (a₁ * a₂) * j⁻¹ :=
      calc a₁⁻¹ * a₂ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) := by rw [hj₁, hj₂]
        _ = j * (a₁ * a₂) * j⁻¹ := by group
    have h1 : (j * y * j⁻¹) * (a₁⁻¹ * a₂) = j * (y * (a₁ * a₂)) * j⁻¹ := by
      rw [hp]; group
    have h2 : (a₁⁻¹ * a₂) * (j * y * j⁻¹) = j * ((a₁ * a₂) * y) * j⁻¹ := by
      rw [hp]; group
    rw [h1, h2, hyc]
  have h := hyp51At_fused_of_cent hP F.invFirst hy' hyc'
  have e : a₁⁻¹ * a₂ * (a₃ * a₄) = a₁ * a₂ * t * (a₃ * a₄) := by rw [F.inv_mul]
  have hcl : Subgroup.closure ({a₁⁻¹ * a₂, t, a₃ * a₄} : Set Y) =
      Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
    have h1 : a₁⁻¹ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
      rw [F.inv_mul]; exact Subgroup.mul_mem _ hpB htB
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      exacts [h1, htB, hqB]
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · have : a₁ * a₂ = (a₁⁻¹ * a₂) * t := by rw [F.inv_mul, mul_assoc _ t t, F.tsq, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  rw [hcl, e] at h
  exact h

@[expose] def V3FourthAlphaF (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
        K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K → K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ →
        a₁ ∈ K → orderOf a₁ = 4 →
        a₂ ∈ K' → orderOf a₂ = 4 → a₃ ∈ K₃ → orderOf a₃ = 4 → a₄ ∈ K₄ → orderOf a₄ = 4 →
        a₁ * a₂ = a₂ * a₁ → a₁ * a₃ = a₃ * a₁ → a₁ * a₄ = a₄ * a₁ → a₂ * a₃ = a₃ * a₂ →
        a₂ * a₄ = a₄ * a₂ → a₃ * a₄ = a₄ * a₃ → y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄ →
        y * t * y⁻¹ ≠ t → y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) → (∃ j : Y, j * a₁ * j⁻¹ = a₁⁻¹ ∧ j * a₂ * j⁻¹ = a₂ ∧ j * a₃ * j⁻¹ = a₃ ∧ j * a₄ * j⁻¹ = a₄) →
          alphaOf (Subgroup.closure ({t, y * t * y⁻¹} : Set Y)) =
            alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y))

@[expose] def V3Hyp51StarF (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
        K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K → K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ →
        a₁ ∈ K → orderOf a₁ = 4 →
        a₂ ∈ K' → orderOf a₂ = 4 → a₃ ∈ K₃ → orderOf a₃ = 4 → a₄ ∈ K₄ → orderOf a₄ = 4 →
        a₁ * a₂ = a₂ * a₁ → a₁ * a₃ = a₃ * a₁ → a₁ * a₄ = a₄ * a₁ → a₂ * a₃ = a₃ * a₂ →
        a₂ * a₄ = a₄ * a₂ → a₃ * a₄ = a₄ * a₃ → y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄ →
        y * t * y⁻¹ ≠ t → y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y) → (∃ j : Y, j * a₁ * j⁻¹ = a₁⁻¹ ∧ j * a₂ * j⁻¹ = a₂ ∧ j * a₃ * j⁻¹ = a₃ ∧ j * a₄ * j⁻¹ = a₄) →
          Hyp51 (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y))

set_option maxHeartbeats 1600000 in
theorem hyp51_starF_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n) (hP : PerpHypS n Y R S t)
    (F : StarFrame (CoreAssembly.conjClass (tightCore R)) t K K' K₃ K₄ a₁ a₂ a₃ a₄) {y j : Y}
    (hy : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄) (hyc : y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y))
    (hj₁ : j * a₁ * j⁻¹ = a₁⁻¹) (hj₂ : j * a₂ * j⁻¹ = a₂) (hj₃ : j * a₃ * j⁻¹ = a₃)
    (hj₄ : j * a₄ * j⁻¹ = a₄) :
    Hyp51 (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) := by
  have hsolv := hsolv_conjClass hP
  have hB := F.isElemAbelian
  refine ⟨hB, F.natCard, fun c hc hc1 => ?_⟩
  have hpB : a₁ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hqB : a₃ * a₄ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  rcases F.mem_cases hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · rw [e]; exact star_vertexY hSp hD4 hM12 h4 hP F
  · rw [e]
    exact hyp51At_of_twin_pair F.hyp hsolv F.hK F.hK' F.hzK F.hzK' F.h₁ F.h₂ hB htB hpB
      F.hzK.ne_one F.p_ne_one F.p_ne_t
  ·
    rw [e]
    have h := star_vertexY hSp hD4 hM12 h4 hP F.swap
    have hset : ({a₃ * a₄, t, a₁ * a₂} : Set Y) = ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at h
    exact h
  ·
    rw [e, ← F.inv_mul]
    have h := star_vertexY hSp hD4 hM12 h4 hP F.invFirst
    have hcl : Subgroup.closure ({a₁⁻¹ * a₂, t, a₃ * a₄} : Set Y) =
        Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
      have h1 : a₁⁻¹ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
        rw [F.inv_mul]; exact Subgroup.mul_mem _ hpB htB
      refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
      · intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        exacts [h1, htB, hqB]
      · intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · have : a₁ * a₂ = (a₁⁻¹ * a₂) * t := by rw [F.inv_mul, mul_assoc _ t t, F.tsq, mul_one]
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
    rw [hcl] at h
    exact h
  · rw [e]; exact hyp51At_fused_of_cent hP F hy hyc
  ·
    have e' : c = a₃⁻¹ * a₄ := by
      rw [e, F.swap.inv_mul]
      exact F.swap.pt_comm.symm
    rw [e']
    have h := star_vertexY hSp hD4 hM12 h4 hP F.swap.invFirst
    have hset : ({a₃⁻¹ * a₄, t, a₁ * a₂} : Set Y) = ({a₃⁻¹ * a₄, t, a₁ * a₂} : Set Y) := rfl
    have hcl : Subgroup.closure ({a₃⁻¹ * a₄, t, a₁ * a₂} : Set Y) =
        Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
      have h1 : a₃⁻¹ * a₄ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
        rw [F.swap.inv_mul]; exact Subgroup.mul_mem _ hqB htB
      refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
      · intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        exacts [h1, htB, hpB]
      · intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · have : a₃ * a₄ = (a₃⁻¹ * a₄) * t := by
            rw [F.swap.inv_mul, mul_assoc _ t t, F.tsq, mul_one]
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
    rw [hcl] at h
    exact h
  · rw [e]; exact hyp51At_fusedT_of_cent hP F hy hyc hj₁ hj₂ hj₃ hj₄

end Gen

section Fam

variable {n : ℕ}

theorem v3FourthAlphaF_of_star {n : ℕ} (h51 : V3Hyp51B n) (hS : V3Hyp51StarF n) :
    V3FourthAlphaF n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₁ a₂ a₃ a₄ y hK₄ h41 h42 h43 h1 o1 h2 o2 h3 o3 h4 o4 c12 c13 c14
    c23 c24 c34 hy hne hyc hj
  have hd := hStd.datum
  have hα := alphaConst h51 hStd.perp hStd.two hStd.exit
  have hz : IsUniqueInvolution K t := hd.hz
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hz hK₄
  have core : A7T22.Hyp22Core (CoreAssembly.conjClass (tightCore R)) K K' K₃ t a₁ a₂ a₃ :=
    ⟨hd.hyp, hd.mem, hd.hK'.1, hd.hK₃.1, hz, hd.hzK', hd.hzK₃, hd.hne, hd.hK₃K, hd.hK₃K',
      ⟨h1, o1⟩, ⟨h2, o2⟩, ⟨h3, o3⟩, c12, c13, c23⟩
  have d' := A7T22.Hyp22G.of_core core hd.subn
  have hB := hS Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₁ a₂ a₃ a₄ y hK₄ h41 h42 h43 h1 o1 h2 o2 h3 o3 h4 o4 c12 c13
    c14 c23 c24 c34 hy hne hyc hj
  have hA₀ : IsElemAbelian2 (Subgroup.closure ({a₁ * a₂, t} : Set Y)) 2 :=
    d'.isElemAbelian2_closure
  have hA₀B : Subgroup.closure ({a₁ * a₂, t} : Set Y) ≤
      Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hcomm : ∀ x, x ∈ K → Commute t x := fun x hx => hz.commute_of_mem hx
  have hct : Commute t (a₁ * a₂ * a₃ * a₄) :=
    (((hcomm a₁ h1).mul_right (hd.hzK'.commute_of_mem h2)).mul_right
      (hd.hzK₃.commute_of_mem h3)).mul_right (hz4.commute_of_mem h4)
  have ht2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ht1 : y * t * y⁻¹ ≠ 1 := by
    intro e
    apply hz.ne_one
    have : t = y⁻¹ * (y * t * y⁻¹) * y := by group
    rw [this, e]; group
  have hA : IsElemAbelian2 (Subgroup.closure ({t, y * t * y⁻¹} : Set Y)) 2 := by
    refine T7A.isElemAbelian2_closure_pair hz.sq ht2 hz.ne_one ht1 (Ne.symm hne) ?_
    rw [hy]
    exact hct.eq
  have hAB : Subgroup.closure ({t, y * t * y⁻¹} : Set Y) ≤
      Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · rw [hy, show a₁ * a₂ * a₃ * a₄ = (a₁ * a₂) * (a₃ * a₄) by group]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have e1 := (lemma54_odd_and_eq hB hA₀B hA₀).2 _ hAB hA
  have e2 := hd.alpha_eq_of_datum hα d'
  rw [e1]
  have e3 : Subgroup.closure ({a₁ * a₂, t} : Set Y) = Subgroup.closure ({a₁ * a₂, t} : Set Y) := rfl
  exact e2.symm
theorem v3Fourth_of_alphaF {n : ℕ} (hα : V3FourthAlphaF n) : V3Fourth n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hP := hC.partIHypG
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hnc : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      (∃ ρ : Rep (CoreAssembly.conjClass (tightCore R)) W, ρ.K = K) →
        ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W :=
    fun W hW ⟨ρ₀, hρ₀⟩ => not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀ (hStd.wyl W hW)
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := exists_fourth_twin' hP hd hperp hnc
  obtain ⟨a₁, a₂, a₃, a₄, y, h1, o1, h2, o2, h3, o3, h4, o4, c12, c13, c14, c23, c24, c34, hy, hne, hyc, hj⟩ :=
    exists_fuse_cent2 hP hd hperp hK₄ h41 h42 h43 hStd.wyl
  exact ⟨K₄, hK₄, h41, h42, h43, y, a₁, a₂, a₃, a₄, h1, o1, h2, o2, h3, o3, h4, o4, c12, c13, c14,
    c23, c24, c34, hy,
    hα Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₁ a₂ a₃ a₄ y hK₄ h41 h42 h43 h1 o1 h2 o2 h3 o3 h4 o4 c12 c13 c14 c23 c24
      c34 hy hne hyc hj⟩

theorem v3Hyp51StarF_of_model (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n) : V3Hyp51StarF n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₁ a₂ a₃ a₄ y hK₄ h41 h42 h43 h1 o1 h2 o2 h3 o3 h4' o4
    c12 c13 c14 c23 c24 c34 hy hne hyc hj
  have hd := hStd.datum
  have hz : IsUniqueInvolution K t := hd.hz
  have ht1 : y * t * y⁻¹ ≠ 1 := by
    intro e
    apply hz.ne_one
    have : t = y⁻¹ * (y * t * y⁻¹) * y := by group
    rw [this, e]; group
  have FR : StarFrame (CoreAssembly.conjClass (tightCore R)) t K K' K₃ K₄ a₁ a₂ a₃ a₄ :=
    { hyp := hd.hyp, hK := hd.mem, hK' := hd.hK'.1, hK₃ := hd.hK₃.1, hK₄ := hK₄.1, hzK := hz,
      hzK' := hd.hzK', hzK₃ := hd.hzK₃, hzK₄ := isUniqueInvolution_of_mem_twinSet hz hK₄,
      n12 := hd.hne, n13 := hd.hK₃K, n23 := hd.hK₃K', n14 := h41, n24 := h42, n34 := h43,
      h₁ := h1, h₂ := h2, h₃ := h3, h₄ := h4', o₁ := o1, o₂ := o2, o₃ := o3, o₄ := o4,
      c12 := c12, c13 := c13, c14 := c14, c23 := c23, c24 := c24, c34 := c34,
      t1 := by rw [← hy]; exact ht1, tt := by rw [← hy]; exact hne }
  obtain ⟨j, hj₁, hj₂, hj₃, hj₄⟩ := hj
  exact hyp51_starF_of_model hSp hD4 hM12 h4 hStd.perp FR hy hyc hj₁ hj₂ hj₃ hj₄

end Fam

end Seven

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
