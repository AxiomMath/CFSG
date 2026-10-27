module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.LieType.Universal CFSG.AGLEmbeddingD2.ParabLevi CFSG.Open CFSG.AGLEmbedding

section Assembly

variable {K Y : Type} [Group K] [Group Y] (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K)
  (π : K →* Y) (I : Set (Fin D.rank))

theorem leviOb_of_blocks {β : Type} [Fintype β] (G C E : β → Subgroup K)
    (hT : Group.IsSolvable ↥(⨆ k, H k))
    (hG : ∀ b, G b ≤ leviM D I) (hcover : leviM D I ≤ ⨆ b, G b)
    (hEG : ∀ b, E b ≤ G b) (hCG : ∀ b, C b ≤ G b) (hdec : ∀ b, G b ≤ E b ⊔ C b)
    (hcomm : ∀ b b', b ≠ b' → G b ≤ Subgroup.centralizer (G b' : Set K))
    (hEsol : ∀ b, Group.IsSolvable ↥(E b))
    (hEC : ∀ b, E b ≤ Subgroup.normalizer (C b : Set K))
    (hTE : ∀ b, (⨆ k, H k) ≤ Subgroup.normalizer (E b : Set K))
    (hTC : ∀ b, (⨆ k, H k) ≤ Subgroup.normalizer (C b : Set K))
    (hCq : ∀ b, C b ≠ ⊥ → CFSG.IsQuasisimple ↥((C b).map π) ∧
      IsClassicalTwoOrG2 (↥((C b).map π) ⧸ Subgroup.center ↥((C b).map π))) :
    LeviOb D H π I := by
  classical
  let ι := {b : β // C b ≠ ⊥}
  let e := Fintype.equivFin ι
  let C' : Fin (Fintype.card ι) → Subgroup K := fun j => C (e.symm j).1
  let E0 : Subgroup K := ⨆ b, E b
  have hE0sol : Group.IsSolvable ↥E0 :=
    isSolvable_iSup_of_commute E hEsol fun b b' hbb' =>
      (hEG b).trans ((hcomm b b' hbb').trans (Subgroup.centralizer_le (hEG b')))
  have hTn : (⨆ k, H k) ≤ Subgroup.normalizer (E0 : Set K) :=
    CFSG.LieType.Steinberg.le_normalizer_iSup hTE
  have hEs : Group.IsSolvable ↥(E0 ⊔ ⨆ k, H k) := isSolvable_sup_of_normalizes' hE0sol hT hTn
  have hE0le : E0 ≤ leviM D I := iSup_le fun b => (hEG b).trans (hG b)
  refine ⟨Fintype.card ι, C', E0 ⊔ ⨆ k, H k, le_sup_right, ?_, hEs, ?_, ?_, ?_⟩
  · exact sup_le (hE0le.trans le_sup_right) le_sup_left
  · intro j
    have hb := (e.symm j).2
    refine ⟨(hCG _).trans (hG _), sup_le (iSup_le fun b => ?_) (hTC _), hCq _ hb⟩
    by_cases hbb : b = (e.symm j).1
    · rw [hbb]; exact hEC _
    · exact ((hEG b).trans ((hcomm b _ hbb).trans (Subgroup.centralizer_le (hCG _)))).trans
        (Subgroup.centralizer_le_normalizer _)
  · intro i j hij
    have hne : (e.symm i).1 ≠ (e.symm j).1 := fun h =>
      hij (e.symm.injective (Subtype.ext h))
    exact (hCG _).trans ((hcomm _ _ hne).trans (Subgroup.centralizer_le (hCG _)))
  · refine hcover.trans (iSup_le fun b => (hdec b).trans (sup_le ?_ ?_))
    · exact (le_iSup E b).trans (le_sup_left.trans le_sup_left)
    · by_cases hb : C b = ⊥
      · rw [hb]; exact bot_le
      · have : C b = C' (e ⟨b, hb⟩) := by simp [C']
        rw [this]
        exact (le_iSup C' (e ⟨b, hb⟩)).trans le_sup_right

end Assembly


section BD

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem rankOne_le_sup_commutator
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {G : Subgroup K} {i : Fin D.rank}
    (hLG : rankOne D.rootGroup i ≤ G)
    (hcyc : ∀ y ∈ D.rootGroup (-Pi.single i 1), ∀ z ∈ D.rootGroup (-Pi.single i 1),
      y ≠ 1 → z = 1 ∨ z = y) :
    rankOne D.rootGroup i ≤ D.rootGroup (Pi.single i 1) ⊔ ⁅G, G⁆ := by
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hroot : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := hΦ.single_mem i
  refine sup_le le_sup_left ?_
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact one_mem _
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ D.rootGroup (Pi.single i 1), x ≠ 1 := by
    by_contra h
    push Not at h
    exact hext.ne_bot _ hroot (Subgroup.eq_bot_iff_forall _ |>.mpr h)
  have hy := hct.conj_mem i _ hroot x hx
  rw [weylAction_simple_single] at hy
  have hy1 : n i * x * (n i)⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x = (n i)⁻¹ * (n i * x * (n i)⁻¹) * n i := by group
    rw [e, h]; simp
  have hzy : z = n i * x * (n i)⁻¹ := (hcyc _ hy _ hz hy1).resolve_left hz1
  have hn : n i ∈ G := hLG (hct.n_mem i)
  have hxG : x ∈ G := hLG (Subgroup.mem_sup_left hx)
  have hcomm : ⁅n i, x⁆ ∈ ⁅G, G⁆ := Subgroup.commutator_mem_commutator hn hxG
  have : z = ⁅n i, x⁆ * x := by rw [hzy, commutatorElement_def]; group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hx)

theorem isSolvable_iSup_simple [Finite K] (hext : SteinbergExtras D n H)
    (hp : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) (J : Set (Fin D.rank)) :
    Group.IsSolvable ↥(⨆ i ∈ J, D.rootGroup (Pi.single i 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have h2 : IsPGroup 2 ↥(⨆ i ∈ J, D.rootGroup (Pi.single i 1)) := by
    refine (isPGroup_iSup_pos hext hp).to_le (iSup₂_le fun i _ => ?_)
    refine le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}) => D.rootGroup γ)
      (Pi.single i 1) ⟨hΦ.single_mem i, ?_⟩ le_rfl
    simp [ht]
  have := h2.isNilpotent
  infer_instance

end BD


section Helpers

open scoped commutatorElement

theorem le_normalizer_commutator {K : Type} [Group K] {G A : Subgroup K}
    (h : A ≤ Subgroup.normalizer (G : Set K)) : A ≤ Subgroup.normalizer ((⁅G, G⁆ : Subgroup K) : Set K) := by
  have key : ∀ x ∈ A, ∀ z ∈ ⁅G, G⁆, x * z * x⁻¹ ∈ ⁅G, G⁆ := by
    intro x hx z hz
    have hconj : ∀ g ∈ G, x * g * x⁻¹ ∈ G := fun g hg =>
      (Subgroup.mem_normalizer_iff.mp (h hx) g).mp hg
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨g1, hg1, g2, hg2, rfl⟩ := hw
      have : x * ⁅g1, g2⁆ * x⁻¹ = ⁅x * g1 * x⁻¹, x * g2 * x⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (hconj g1 hg1) (hconj g2 hg2)
    | one => simp
    | mul a b _ _ ha hb =>
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  exact ⟨fun hz => key x hx z hz, fun hz => by
    have := key x⁻¹ (inv_mem hx) _ hz
    simpa [mul_assoc] using this⟩

theorem chev_map_of_equiv {K Y : Type} [Group K] [Group Y] (π : K →* Y)
    (hπ : Function.Injective π) {C : Subgroup K} {M : Type} [Group M] (e : M ≃* ↥C)
    (h : CFSG.IsQuasisimple M ∧ IsClassicalTwoOrG2 (M ⧸ Subgroup.center M)) :
    CFSG.IsQuasisimple ↥(C.map π) ∧
      IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π)) := by
  let e' : M ≃* ↥(C.map π) := e.trans (C.equivMapOfInjective π hπ)
  exact ⟨isQuasisimple_of_mulEquiv e' h.1,
    isClassicalTwoOrG2_of_mulEquiv (CFSG.Quasithin.SmithC27.quotCenterCongr e') h.2⟩

end Helpers


section Decomp

variable {K Y : Type} [Group K] [Group Y] (π : K →* Y) (A G : Subgroup K)

theorem le_normalizer_bot (B : Subgroup K) : B ≤ Subgroup.normalizer ((⊥ : Subgroup K) : Set K) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl; simp
  · intro h'; simpa using h'

theorem decomp_ns (hA : A ≤ Subgroup.normalizer (G : Set K))
    (hq : CFSG.IsQuasisimple ↥(G.map π) ∧
      IsClassicalTwoOrG2 (↥(G.map π) ⧸ Subgroup.center ↥(G.map π))) :
    ∃ E C : Subgroup K, E ≤ G ∧ C ≤ G ∧ G ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set K) ∧ A ≤ Subgroup.normalizer (E : Set K) ∧
      A ≤ Subgroup.normalizer (C : Set K) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) :=
  ⟨⊥, G, bot_le, le_rfl, by simp, inferInstance, bot_le, le_normalizer_bot _, hA, fun _ => hq⟩

theorem decomp_so (hA : A ≤ Subgroup.normalizer (G : Set K)) (hs : Group.IsSolvable ↥G) :
    ∃ E C : Subgroup K, E ≤ G ∧ C ≤ G ∧ G ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set K) ∧ A ≤ Subgroup.normalizer (E : Set K) ∧
      A ≤ Subgroup.normalizer (C : Set K) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) :=
  ⟨G, ⊥, le_rfl, bot_le, by simp, hs, le_normalizer_bot _, hA, le_normalizer_bot _, fun h => absurd rfl h⟩

open scoped commutatorElement in
theorem decomp_bd (E : Subgroup K) (hA : A ≤ Subgroup.normalizer (G : Set K))
    (hAE : A ≤ Subgroup.normalizer (E : Set K)) (hEG : E ≤ G) (hGE : G ≤ E ⊔ ⁅G, G⁆)
    (hs : Group.IsSolvable ↥E)
    (hq : CFSG.IsQuasisimple ↥((⁅G, G⁆ : Subgroup K).map π) ∧
      IsClassicalTwoOrG2 (↥((⁅G, G⁆ : Subgroup K).map π) ⧸
        Subgroup.center ↥((⁅G, G⁆ : Subgroup K).map π))) :
    ∃ E' C : Subgroup K, E' ≤ G ∧ C ≤ G ∧ G ≤ E' ⊔ C ∧ Group.IsSolvable ↥E' ∧
      E' ≤ Subgroup.normalizer (C : Set K) ∧ A ≤ Subgroup.normalizer (E' : Set K) ∧
      A ≤ Subgroup.normalizer (C : Set K) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  refine ⟨E, ⁅G, G⁆, hEG, ?_, hGE, hs, ?_, hAE, le_normalizer_commutator hA, fun _ => hq⟩
  · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    simp only [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)
  · exact le_normalizer_commutator (hEG.trans Subgroup.le_normalizer)

end Decomp

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
