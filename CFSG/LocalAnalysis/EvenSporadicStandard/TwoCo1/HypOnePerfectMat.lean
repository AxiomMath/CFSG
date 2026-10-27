module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

theorem forall₂_map_getD0 {R : Native.Rows → GL24 → Prop} {rs : List Native.Rows}
    {gs : List GL24} (h : List.Forall₂ R rs gs) (hd : R Native.one 1) :
    ∀ idx : List ℕ, List.Forall₂ R (idx.map fun j => rs.getD j Native.one)
      (idx.map fun j => gs.getD j 1)
  | [] => .nil
  | j :: idx => .cons (getD_rep h hd j) (forall₂_map_getD0 h hd idx)

theorem forall₂_right_unique {rs : List Native.Rows} {gs hs : List GL24}
    (h1 : List.Forall₂ MRep rs gs) (h2 : List.Forall₂ MRep rs hs) : gs = hs := by
  induction h1 generalizing hs with
  | nil => cases h2; rfl
  | cons hab _ ih =>
    cases h2 with
    | cons hab' h2' => rw [hab.eq hab', ih h2']

theorem forall₂_mem_right {R : Native.Rows → GL24 → Prop} {rs : List Native.Rows}
    {gs : List GL24} (h : List.Forall₂ R rs gs) {r : Native.Rows} (hr : r ∈ rs) :
    ∃ g ∈ gs, R r g := by
  induction h with
  | nil => simp at hr
  | cons hab _ ih =>
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨g, hg, hR⟩ := ih hr
      exact ⟨g, List.mem_cons_of_mem _ hg, hR⟩

theorem rep_pickRows {D : List Native.Rows × List Native.Rows × Bool} {DG : List GL24}
    (h : List.Forall₂ MRep D.1 DG) (idx : List ℕ) :
    List.Forall₂ MRep (pickRows D idx) (idx.map fun j => DG.getD j 1) :=
  forall₂_map_getD0 h MRep.one idx

theorem rep_commRows {D : List Native.Rows × List Native.Rows × Bool} {DG : List GL24}
    (h : List.Forall₂ MRep D.1 DG) {cIdx : List (ℕ × ℕ)}
    (hinv : ∀ ij ∈ cIdx, Native.mul (D.1.getD ij.1 Native.one)
        (Native.inv (D.1.getD ij.1 Native.one)) = Native.one ∧
      Native.mul (D.1.getD ij.2 Native.one) (Native.inv (D.1.getD ij.2 Native.one)) =
        Native.one) :
    List.Forall₂ MRep (commRows D cIdx) (cIdx.map fun ij =>
      (DG.getD ij.1 1)⁻¹ * (DG.getD ij.2 1)⁻¹ * ((DG.getD ij.1 1) * (DG.getD ij.2 1))) := by
  unfold commRows
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun ij hij => ?_
  have hu := getD_rep h MRep.one ij.1
  have hv := getD_rep h MRep.one ij.2
  obtain ⟨hu1, hv1⟩ := hinv ij hij
  exact ((hu.inv hu1).mul (hv.inv hv1)).mul (hu.mul hv)

theorem exists_perfect_of_check {K : Subgroup GL24} {B : List Native.Rows} {BG : List GL24}
    (hrepB : List.Forall₂ MRep B BG) (hBGK : ∀ g ∈ BG, g ∈ K)
    {dP dU dF dQ : List (List ℤ)} {pIdx fIdx qIdx : List ℕ} {cIdx : List (ℕ × ℕ)}
    {Qr : List Native.Rows}
    (h : perfectCheckOf B dP pIdx dU cIdx dF fIdx dQ qIdx Qr = true) :
    ∃ P : Subgroup GL24, P ≤ K ∧ P ≤ ⁅P, P⁆ ∧ ∀ r ∈ Qr, ∀ q : GL24, MRep r q → q ∈ P := by
  simp only [perfectCheckOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hDP, hDU⟩, hDF⟩, hDQ⟩, hCinv⟩, hF⟩, hQ⟩ := h
  have hrepDP := dag_rep hrepB dP hDP
  have hrepP := rep_pickRows hrepDP pIdx
  obtain ⟨PG, hPGdef⟩ : ∃ PG : List GL24, PG = pIdx.map fun j => (dagG BG dP).getD j 1 := ⟨_, rfl⟩
  rw [← hPGdef] at hrepP
  have hPGK : ∀ g ∈ PG, g ∈ K := by
    intro g hg
    rw [hPGdef] at hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact getD_mem_of_forall (dagG_mem hBGK dP) j
  refine ⟨Subgroup.closure {g | g ∈ PG}, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    exact hPGK
  all_goals
    obtain ⟨P, hP⟩ : ∃ P : Subgroup GL24, P = Subgroup.closure {g | g ∈ PG} := ⟨_, rfl⟩
    rw [← hP]
    have hPG : ∀ g ∈ PG, g ∈ P := fun g hg => hP ▸ Subgroup.subset_closure hg
    have hrepDU := dag_rep hrepP dU hDU
    have hUP : ∀ g ∈ dagG PG dU, g ∈ P := dagG_mem hPG dU
  ·
    have hCGmem : ∀ g ∈ cIdx.map (fun ij => ((dagG PG dU).getD ij.1 1)⁻¹ *
        ((dagG PG dU).getD ij.2 1)⁻¹ * (((dagG PG dU).getD ij.1 1) * ((dagG PG dU).getD ij.2 1))),
        g ∈ ⁅P, P⁆ := by
      intro g hg
      obtain ⟨ij, -, rfl⟩ := List.mem_map.1 hg
      have hu := P.inv_mem (getD_mem_of_forall hUP ij.1)
      have hv := P.inv_mem (getD_mem_of_forall hUP ij.2)
      have := Subgroup.commutator_mem_commutator hu hv
      rw [commutatorElement_def, inv_inv, inv_inv, mul_assoc] at this
      exact this
    have hrepC := rep_commRows hrepDU hCinv
    have hrepDF := dag_rep hrepC dF hDF
    have hrepF := rep_pickRows hrepDF fIdx
    rw [hF] at hrepF
    have hPFG := forall₂_right_unique hrepP hrepF
    refine hP.le.trans ((Subgroup.closure_le _).2 fun g hg => ?_)
    rw [hPFG] at hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact getD_mem_of_forall (dagG_mem hCGmem dF) j
  ·
    have hrepDQ := dag_rep hrepP dQ hDQ
    have hrepQ := rep_pickRows hrepDQ qIdx
    rw [hQ] at hrepQ
    intro r hr q hq
    obtain ⟨g, hg, hrg⟩ := forall₂_mem_right hrepQ hr
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    rw [hq.eq hrg]
    exact getD_mem_of_forall (dagG_mem hPG dQ) j

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
