module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Lemma5AuxMat
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Lemma5AuxGrp
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis
open CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 CFSG.RankThree.Lattice
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace L5

@[expose] def rootT (i j : Fin 5) : Fin Tag.E8.rank → ℤ :=
  wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j

theorem rootT_eq (i j : Fin 5) : sigmaRootE8A4 e8VB i j = rootT i j := by
  rw [sigmaRootE8A4_eq_smul, e8VB_smul]
  rfl

theorem frame_data :
    rootT 0 4 = highRoot Tag.E8 ∧ rootT 4 0 = -highRoot Tag.E8 ∧
    (∀ i j : Fin 5, i ≠ j → ¬ LowerPos i j → 0 ≤ rootT i j 7) ∧
    (∀ i j : Fin 5, i ≠ j → PureDir i j → rootT i j 7 = -1 ∧ rootT i j 4 % 5 = 0) := by
  unfold rootT
  decide +kernel

theorem listA_deg : ∀ β ∈ e8ListA, β 7 = 0 := by decide +kernel

theorem sigmaSet_eq : sigmaSetE8A4 e8VB = {r | r ∈ e8ListB} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_setOf_eq, sigmaRootE8A4_eq_smul, e8VB_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8B_img i j hij
  · intro hr
    exact e8B_cover r hr

end L5

theorem lemma5_neg (K : Type) [Field K] [Finite K] {D : Subgroup (ModGL Tag.E8 K)}
    (hD : IsLongRootSubgroup Tag.E8 K D) (hle : D ≤ R1neg K) :
    ∃ y ∈ X1 K, y ∈ Lθ Tag.E8 K ∧ ∃ ν ∈ pureNegDirs,
      conjSub y D ≤ rootSpan Tag.E8 K {ν, -theta} := by
  classical
  obtain ⟨hf1, hf2, hf3, hf4⟩ := L5.frame_data
  obtain ⟨g, hg, hDg⟩ := hD
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SL(5, K) →* ModGL Tag.E8 K, ψ = rhoSigmaE8A4 K e8VB := ⟨_, rfl⟩
  have hinj : Function.Injective ψ := by
    rw [hψ]
    exact rhoSigmaE8A4_injective e8VB
  have hrange : ψ.range = X1 K := by
    rw [hψ, rhoSigmaE8A4_range (L := K) e8VB, L5.sigmaSet_eq]
    rfl
  have hT : ∀ (i j : Fin 5) (hij : i ≠ j), ∃ ε : Kˣ, ∀ t : K,
      ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        pinnedX Tag.E8 K (L5.rootT i j) ((ε : K) * t) := by
    intro i j hij
    obtain ⟨ε, hε⟩ := rhoSigmaE8A4_transvection (L := K) e8VB i j hij
    refine ⟨ε, fun t => ?_⟩
    rw [hψ, hε t, L5.rootT_eq]
  have hX1ad : X1 K ≤ adjointGroup Tag.E8 K := iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hψad : ∀ x : SL(5, K), ψ x ∈ adjointGroup Tag.E8 K := by
    intro x
    have h : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [hrange] at h
    exact hX1ad h
  obtain ⟨ε₀, hε₀⟩ := hT 0 4 (by decide)
  obtain ⟨ε₁, hε₁⟩ := hT 4 0 (by decide)
  have hψ04 : ∀ t : K, ψ (L5.U04 t) = pinnedX Tag.E8 K (highRoot Tag.E8) ((ε₀ : K) * t) := by
    intro t
    have h := hε₀ t
    rw [hf1] at h
    exact h
  have hψ40 : ∀ t : K, ψ (L5.U40 t) = pinnedX Tag.E8 K (-highRoot Tag.E8) ((ε₁ : K) * t) := by
    intro t
    have h := hε₁ t
    rw [hf2] at h
    exact h
  have hlo_gen : ∀ α ∈ R1negRoots, rootSubgroup Tag.E8 K α ≤ (L5.LoSG K).map ψ := by
    intro α hα
    obtain ⟨hαroot, h4, h7⟩ := hα
    have hmemB : α ∈ e8ListB := by
      rcases S_data α (mem_rootFinset.2 hαroot) h4 with hA | hB
      · exfalso
        have := L5.listA_deg α hA
        omega
      · exact hB
    obtain ⟨i, j, hij, hαeq⟩ := e8B_cover α hmemB
    have hαeq' : α = L5.rootT i j := hαeq
    have hlow : L5.LowerPos i j := by
      by_contra hn
      have h0 := hf3 i j hij hn
      rw [← hαeq'] at h0
      omega
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨ε, hε⟩ := hT i j hij
    refine ⟨Matrix.SpecialLinearGroup.transvection hij (((ε⁻¹ : Kˣ) : K) * c),
      L5.transvection_mem_LoSG hij hlow _, ?_⟩
    rw [hε, Units.mul_inv_cancel_left, hαeq']
  have hR1 : R1neg K ≤ (L5.LoSG K).map ψ := iSup₂_le hlo_gen
  have hlo : D.comap ψ ≤ L5.LoSG K := by
    intro d hd
    obtain ⟨M, hM, hMd⟩ := hR1 (hle hd)
    have : M = d := hinj hMd
    rw [← this]
    exact hM
  have hnt : ∃ d ∈ D.comap ψ, d ≠ 1 := by
    have hx : g * pinnedX Tag.E8 K (highRoot Tag.E8) 1 * g⁻¹ ∈ D := by
      rw [hDg, mem_conjSub_iff]
      have e : g⁻¹ * (g * pinnedX Tag.E8 K (highRoot Tag.E8) 1 * g⁻¹) * g =
          pinnedX Tag.E8 K (highRoot Tag.E8) 1 := by group
      rw [e]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    have hx1 : g * pinnedX Tag.E8 K (highRoot Tag.E8) 1 * g⁻¹ ≠ 1 := by
      intro h
      have h1 : pinnedX Tag.E8 K (highRoot Tag.E8) 1 = 1 := by
        calc pinnedX Tag.E8 K (highRoot Tag.E8) 1
            = g⁻¹ * (g * pinnedX Tag.E8 K (highRoot Tag.E8) 1 * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      have h0 := pinnedX_injective Tag.E8 K (highRoot Tag.E8)
        (h1.trans (pinnedX_zero Tag.E8 K _).symm)
      exact one_ne_zero h0
    obtain ⟨M, -, hM⟩ := hR1 (hle hx)
    refine ⟨M, ?_, ?_⟩
    · show ψ M ∈ D
      rw [hM]
      exact hx
    · rintro rfl
      apply hx1
      rw [← hM, map_one]
  have hconjU : ∀ (M : SL(5, K)) (x : ModGL Tag.E8 K),
      x ∈ conjSub (ψ M) (Uθ Tag.E8 K) ↔ ∃ t : K, x = ψ (M * L5.U04 t * M⁻¹) := by
    intro M x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
      refine ⟨(((ε₀⁻¹ : Kˣ) : K)) * c, ?_⟩
      rw [map_mul, map_mul, hψ04, map_inv, Units.mul_inv_cancel_left, hc]
      group
    · rintro ⟨t, rfl⟩
      rw [map_mul, map_mul, hψ04, map_inv]
      have e : (ψ M)⁻¹ * (ψ M * pinnedX Tag.E8 K (highRoot Tag.E8) ((ε₀ : K) * t) * (ψ M)⁻¹) *
          ψ M = pinnedX Tag.E8 K (highRoot Tag.E8) ((ε₀ : K) * t) := by group
      rw [e]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hDlong : ∀ n : SL(5, K), IsLongRootSubgroup Tag.E8 K (conjSub (ψ n) D) := fun n =>
    ⟨ψ n * g, mul_mem (hψad n) hg, by rw [hDg, conjSub_mul]⟩
  have hDich : L5.Dich (D.comap ψ) := by
    intro n
    rcases L5.theta_dichotomy K (hDlong n) with h | ⟨m, hm, hmeq⟩
    · left
      intro d hd t
      have hu : ψ (L5.U04 t) ∈ Uθ Tag.E8 K := by
        rw [hψ04 t]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      have hd' : ψ (n * d * n⁻¹) ∈ conjSub (ψ n) D := by
        rw [mem_conjSub_iff, map_mul, map_mul, map_inv]
        have e : (ψ n)⁻¹ * (ψ n * ψ d * (ψ n)⁻¹) * ψ n = ψ d := by group
        rw [e]
        exact hd
      have hc := h _ hu _ hd'
      rw [← map_commutatorElement, ← map_mul, ← map_mul] at hc
      exact hinj hc
    · right
      have hmr : m ∈ ψ.range := by
        have hUle : Uθ Tag.E8 K ≤ ψ.range := by
          rw [hrange]
          exact Uθ_le_X1 K
        have hDle : conjSub (ψ n) D ≤ ψ.range := by
          intro x hx
          rw [mem_conjSub_iff] at hx
          have hx2 : (ψ n)⁻¹ * x * ψ n ∈ ψ.range := by
            obtain ⟨M, -, hM⟩ := hR1 (hle hx)
            exact ⟨M, hM⟩
          have e : x = ψ n * ((ψ n)⁻¹ * x * ψ n) * (ψ n)⁻¹ := by group
          rw [e]
          exact mul_mem (mul_mem ⟨n, rfl⟩ hx2) (inv_mem ⟨n, rfl⟩)
        exact (sup_le hUle hDle) hm
      obtain ⟨M, rfl⟩ := hmr
      refine ⟨M, fun g' => ?_⟩
      have e1 : ψ g' ∈ D ↔ ψ (n * g' * n⁻¹) ∈ conjSub (ψ n) D := by
        rw [mem_conjSub_iff, map_mul, map_mul, map_inv]
        have e : (ψ n)⁻¹ * (ψ n * ψ g' * (ψ n)⁻¹) * ψ n = ψ g' := by group
        rw [e]
      show ψ g' ∈ D ↔ _
      rw [e1, ← hmeq, hconjU M]
      exact exists_congr fun t => hinj.eq_iff
  obtain ⟨P, hP04, hP40, i, j, hij, hpure, hall⟩ := L5.pure_of_dich (D.comap ψ) hlo hnt hDich
  refine ⟨ψ P, ?_, ?_, L5.rootT i j, ?_, ?_⟩
  · have h : ψ P ∈ ψ.range := ⟨P, rfl⟩
    rwa [hrange] at h
  · refine Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.E8 K (hψad P) ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      have h1 : pinnedX Tag.E8 K (highRoot Tag.E8) c =
          ψ (L5.U04 (((ε₀⁻¹ : Kˣ) : K) * c)) := by
        rw [hψ04, Units.mul_inv_cancel_left]
      rw [h1, ← map_mul, ← map_mul, hP04]
    · intro x hx
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
      have h1 : pinnedX Tag.E8 K (-highRoot Tag.E8) c =
          ψ (L5.U40 (((ε₁⁻¹ : Kˣ) : K) * c)) := by
        rw [hψ40, Units.mul_inv_cancel_left]
      rw [h1, ← map_mul, ← map_mul, hP40]
  · have hroot : IsRoot Tag.E8 (L5.rootT i j) := by
      rw [← L5.rootT_eq]
      exact isRoot_sigmaRootE8A4 e8VB hij
    obtain ⟨h7, h4⟩ := hf4 i j hij hpure
    exact mem_pureNegDirs.2 ⟨hroot, h7, h4⟩
  · intro x hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨d, -, hd⟩ := hR1 (hle hx)
    have hdD : d ∈ D.comap ψ := by
      show ψ d ∈ D
      rw [hd]
      exact hx
    obtain ⟨u, v, huv⟩ := hall d hdD
    have hxeq : x = ψ (P * d * P⁻¹) := by
      rw [map_mul, map_mul, map_inv, hd]
      group
    obtain ⟨εij, hεij⟩ := hT i j hij
    rw [hxeq, huv, map_mul, hεij u, hψ40 v]
    refine mul_mem (pinnedX_mem_rootSpan (Set.mem_insert _ _) _)
      (pinnedX_mem_rootSpan ?_ _)
    rw [← theta_eq]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
