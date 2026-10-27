module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
public import CFSG.ClassicalInvolution.Q3.Q3T6LinSp
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRed
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open Matrix
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}

theorem perfectInLayer_conj_statedSp {p : ℕ} (hℓ : 1 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ↥(StatedSp ℓ F)) (hx : x ^ p = 1) : PerfectInLayer (MulAut.conj x) := by
  haveI : NeZero ℓ := ⟨by omega⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _, hcard⟩ := FiniteField.card F 2
  have hcard' : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hinj, hsurj⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo (r := ℓ) (K := F)
  let e : ↥(StatedSp ℓ F) ≃* StatedProj (StatedSp ℓ F) :=
    MulEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine perfectInLayer_of_congr e (MulAut.conj x) ?_
  have hcongr : MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [hcongr]
  exact perfectInLayer_conj_sp Nat.prime_two (by exact_mod_cast n.pos) hcard'
    hℓ hp hp2 hp2 x hx

theorem le_stdLayer_of_perfect {p : ℕ} (hℓ : 1 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ↥(StatedSp ℓ F)) (hx : x ^ p = 1) {X : Subgroup ↥(StatedSp ℓ F)}
    (hXc : X ≤ Subgroup.centralizer ({x} : Set ↥(StatedSp ℓ F))) (hXp : ⁅X, X⁆ = X) :
    X ≤ stdLayer x := by
  have hfix := CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj x
  have h := perfectInLayer_conj_statedSp hℓ hp hp2 x hx X (by rwa [hfix]) hXp
  simpa [stdLayer, hfix] using h

private theorem spEnd_spEmbed_pairMap_permSp_swap {j₁ j₂ : Fin ℓ}
    (hσ : Function.Injective (pairMap j₁ j₂)) :
    spEnd (spEmbed (pairMap j₁ j₂) hσ
        (CFSG.SeitzReduction.SymplecticPilot.permSp F (Equiv.swap (0 : Fin 2) 1)))
      (Pi.single (Sum.inl j₁) 1) = Pi.single (Sum.inl j₂) 1 := by
  rw [spEnd_apply, ← mat_apply, mat_spEmbed, CFSG.SeitzReduction.SymplecticPilot.mat_permSp]
  funext a
  rw [mulVec_single_one_apply]
  by_cases ha : a = Sum.inl j₂
  · subst ha
    have himage := spEmbedMat_apply_image hσ
      (g := spIncl (K := F) (⇑(Equiv.swap (0 : Fin 2) 1)))
      (x := Sum.inl 1) (y := Sum.inl 0)
    simp only [pairMap_zero, pairMap_one, Sum.map_inl] at himage
    rw [himage, spIncl_apply]
    simp
  · have hsingle : (Pi.single (Sum.inl j₂) (1 : F) : Fin ℓ ⊕ Fin ℓ → F) a = 0 := by
      rw [Pi.single_apply, if_neg ha]
    rw [hsingle]
    by_cases hmem : a ∈ Set.range (Sum.map (pairMap j₁ j₂) (pairMap j₁ j₂))
    · obtain ⟨x, rfl⟩ := hmem
      have himage := spEmbedMat_apply_image hσ
        (g := spIncl (K := F) (⇑(Equiv.swap (0 : Fin 2) 1)))
        (x := x) (y := Sum.inl 0)
      simp only [pairMap_zero, Sum.map_inl] at himage
      rw [himage, spIncl_apply]
      have hx : x ≠ Sum.inl 1 := fun h => ha (by rw [h]; simp [pairMap])
      simp [hx]
    · rw [spEmbedMat_apply_of_not_mem _ (fun h => hmem h.1), Matrix.one_apply]
      have hne : a ≠ Sum.inl j₁ := fun h => hmem ⟨Sum.inl 0, by rw [h]; simp [pairMap]⟩
      simp [hne]

theorem exists_perfect_le_centralizer_diagSp (hF : 4 ≤ Nat.card F) {j₁ j₂ : Fin ℓ}
    (hj : j₁ ≠ j₂) :
    ∃ X : Subgroup ↥(StatedSp ℓ F), ⁅X, X⁆ = X ∧
      (∀ t : Fin ℓ → Fˣ, t j₁ = 1 → t j₂ = 1 →
        X ≤ Subgroup.centralizer
          ({CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t} : Set ↥(StatedSp ℓ F))) ∧
      ∃ g ∈ X, spEnd g (Pi.single (Sum.inl j₁) 1) = Pi.single (Sum.inl j₂) 1 := by
  classical
  obtain ⟨hσ⟩ : ∃ hσ : Function.Injective (pairMap j₁ j₂), True :=
    ⟨pairMap_injective hj, trivial⟩
  refine ⟨(spEmbed (pairMap j₁ j₂) hσ).range, ?_, ?_, ?_⟩
  · have htop : ⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ = ⊤ :=
      (CFSG.ClassicalInvolution.Q3.Q3T6.isPerfect_sp4_of_three_le (by omega)).commutator_eq_top
    rw [MonoidHom.range_eq_map (spEmbed (pairMap j₁ j₂) hσ), ← Subgroup.map_commutator, htop]
  · intro t h1 h2 y hy
    obtain ⟨g, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsupp : spEmbed (pairMap j₁ j₂) hσ g ∈
        suppGroup (Set.range (Sum.map (pairMap j₁ j₂) (pairMap j₁ j₂))) :=
      mem_suppGroup.2 (isSupp_spEmbed hσ g)
    have hentry : ∀ a ∈ Set.range (Sum.map (pairMap j₁ j₂) (pairMap j₁ j₂)),
        CFSG.SeitzReduction.SymplecticPilot.diagSpEntry t a = 1 := by
      rintro _ ⟨x, rfl⟩
      rcases x with l | l
      · fin_cases l
        · simp [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry, pairMap, h1]
        · simp [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry, pairMap, h2]
      · fin_cases l
        · simp [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry, pairMap, h1]
        · simp [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry, pairMap, h2]
    exact (CFSG.SeitzReduction.SymplecticPilot.commute_diagSp_of_mem_suppGroup
      (fun a ha b hb => (hentry a ha).trans (hentry b hb).symm) hsupp).eq
  · exact ⟨spEmbed (pairMap j₁ j₂) hσ
        (CFSG.SeitzReduction.SymplecticPilot.permSp F (Equiv.swap (0 : Fin 2) 1)),
      ⟨_, rfl⟩, spEnd_spEmbed_pairMap_permSp_swap hσ⟩

private theorem mat_eq_diagonal_of_preserves_lines {k : ↥(StatedSp ℓ F)}
    (h : ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ c : F, spEnd k (Pi.single b 1) = c • Pi.single b 1) :
    mat ℓ F k = Matrix.diagonal (fun b => mat ℓ F k b b) := by
  ext i j
  obtain ⟨c, hc⟩ := h j
  have hcol : mat ℓ F k i j = c * (if i = j then 1 else 0) := by
    have := congrFun hc i
    rw [spEnd_apply, ← mat_apply, mulVec_single_one_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul] at this
    exact this
  rcases eq_or_ne i j with hij | hij
  · subst hij
    rw [Matrix.diagonal_apply, if_pos rfl]
  · rw [hcol, Matrix.diagonal_apply, if_neg hij, if_neg hij, mul_zero]

theorem mul_comm_of_forall_preserves_lines {K : Subgroup ↥(StatedSp ℓ F)}
    (h : ∀ k ∈ K, ∀ b : Fin ℓ ⊕ Fin ℓ, ∃ c : F,
      spEnd k (Pi.single b 1) = c • Pi.single b 1) :
    ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  intro a ha b hb
  apply mat_injective
  have haD := mat_eq_diagonal_of_preserves_lines (fun b' => h a ha b')
  have hbD := mat_eq_diagonal_of_preserves_lines (fun b' => h b hb b')
  rw [map_mul, map_mul, haD, hbD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => mat ℓ F a i i * mat ℓ F b i i) =
      (fun i => mat ℓ F b i i * mat ℓ F a i i) := by
    funext i
    exact mul_comm _ _
  rw [hfun]

private theorem spEnd_diagSp_single_inl (t : Fin ℓ → Fˣ) (i : Fin ℓ) :
    spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t) (Pi.single (Sum.inl i) 1) =
      (t i : F) • Pi.single (Sum.inl i) 1 := by
  rw [spEnd_apply, ← mat_apply]
  funext a
  rw [mulVec_single_one_apply, CFSG.SeitzReduction.SymplecticPilot.mat_diagSp_apply]
  by_cases ha : a = Sum.inl i
  · subst ha
    simp
  · rw [if_neg ha, Pi.smul_apply, Pi.single_eq_of_ne ha, smul_zero]

private theorem spEnd_diagSp_single_inr (t : Fin ℓ → Fˣ) (i : Fin ℓ) :
    spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t) (Pi.single (Sum.inr i) 1) =
      ((t i)⁻¹ : F) • Pi.single (Sum.inr i) 1 := by
  rw [spEnd_apply, ← mat_apply]
  funext a
  rw [mulVec_single_one_apply, CFSG.SeitzReduction.SymplecticPilot.mat_diagSp_apply]
  by_cases ha : a = Sum.inr i
  · subst ha
    simp
  · rw [if_neg ha, Pi.smul_apply, Pi.single_eq_of_ne ha, smul_zero]

private theorem inv_ne_self_of_ne_one {t : Fˣ} (ht : t ≠ 1) : t⁻¹ ≠ t := by
  intro h
  have hsq : t * t = 1 := by simpa [h] using mul_inv_cancel t
  have hF : (t : F) * (t : F) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hsq
    simpa using this
  have h1 : (t : F) = 1 := by
    rcases mul_self_eq_one_iff.mp hF with h1 | h1
    · exact h1
    · rwa [CharTwo.neg_eq] at h1
  exact ht (Units.ext h1)

private theorem spEnd_single_inl_eq_smul_of_mem {K : Subgroup ↥(StatedSp ℓ F)}
    {t : Fin ℓ → Fˣ}
    (hKd : K ≤ Subgroup.centralizer
      ({CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t} : Set ↥(StatedSp ℓ F)))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) 1) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) 1) ∈ stdPlane F ℓ i)
    {i : Fin ℓ} (hti : t i ≠ 1) {k : ↥(StatedSp ℓ F)} (hk : k ∈ K) :
    spEnd k (Pi.single (Sum.inl i) 1) =
      ((spEnd k (Pi.single (Sum.inl i) 1)) (Sum.inl i)) • Pi.single (Sum.inl i) 1 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hpl k hk i).1
  have hzero := (CFSG.SeitzReduction.SymplecticPilot.commute_diagSp_iff k t).1
    (Subgroup.mem_centralizer_singleton_iff.1 (hKd hk))
  have hb0 : b = 0 := by
    have hb : b = mat ℓ F k (Sum.inr i) (Sum.inl i) := by
      have h := congrFun hab (Sum.inr i)
      simpa [spEnd_apply, ← mat_apply, mulVec_single_one_apply, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne Sum.inr_ne_inl, smul_eq_mul] using h
    rw [hb]
    refine hzero (Sum.inr i) (Sum.inl i) ?_
    intro h
    exact inv_ne_self_of_ne_one hti
      (Units.ext (by simpa [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry] using h))
  rw [← hab, hb0, zero_smul, add_zero]
  ext x
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hx : x = Sum.inl i
  · subst hx
    simp
  · simp [hx]

private theorem spEnd_single_inr_eq_smul_of_mem {K : Subgroup ↥(StatedSp ℓ F)}
    {t : Fin ℓ → Fˣ}
    (hKd : K ≤ Subgroup.centralizer
      ({CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t} : Set ↥(StatedSp ℓ F)))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) 1) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) 1) ∈ stdPlane F ℓ i)
    {i : Fin ℓ} (hti : t i ≠ 1) {k : ↥(StatedSp ℓ F)} (hk : k ∈ K) :
    spEnd k (Pi.single (Sum.inr i) 1) =
      ((spEnd k (Pi.single (Sum.inr i) 1)) (Sum.inr i)) • Pi.single (Sum.inr i) 1 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hpl k hk i).2
  have hzero := (CFSG.SeitzReduction.SymplecticPilot.commute_diagSp_iff k t).1
    (Subgroup.mem_centralizer_singleton_iff.1 (hKd hk))
  have ha0 : a = 0 := by
    have ha : a = mat ℓ F k (Sum.inl i) (Sum.inr i) := by
      have h := congrFun hab (Sum.inl i)
      simpa [spEnd_apply, ← mat_apply, mulVec_single_one_apply, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne Sum.inl_ne_inr, smul_eq_mul] using h
    rw [ha]
    refine hzero (Sum.inl i) (Sum.inr i) ?_
    intro h
    exact (inv_ne_self_of_ne_one hti).symm
      (Units.ext (by simpa [CFSG.SeitzReduction.SymplecticPilot.diagSpEntry] using h))
  rw [← hab, ha0, zero_smul, zero_add]
  ext x
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hx : x = Sum.inr i
  · subst hx
    simp
  · simp [hx]

private theorem spEnd_single_inl_apply_ne_zero {k : ↥(StatedSp ℓ F)} {i : Fin ℓ}
    (hke : spEnd k (Pi.single (Sum.inl i) 1) =
      ((spEnd k (Pi.single (Sum.inl i) 1)) (Sum.inl i)) • Pi.single (Sum.inl i) 1) :
    (spEnd k (Pi.single (Sum.inl i) 1)) (Sum.inl i) ≠ 0 := by
  intro h0
  have hz : spEnd k (Pi.single (Sum.inl i) 1) = 0 := by rw [hke, h0, zero_smul]
  have hleft : spEnd k⁻¹ (spEnd k (Pi.single (Sum.inl i) 1)) = Pi.single (Sum.inl i) 1 := by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  rw [hz, map_zero] at hleft
  exact (Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : F) ≠ 0)) hleft.symm

private theorem spEnd_single_inr_apply_ne_zero {k : ↥(StatedSp ℓ F)} {i : Fin ℓ}
    (hkf : spEnd k (Pi.single (Sum.inr i) 1) =
      ((spEnd k (Pi.single (Sum.inr i) 1)) (Sum.inr i)) • Pi.single (Sum.inr i) 1) :
    (spEnd k (Pi.single (Sum.inr i) 1)) (Sum.inr i) ≠ 0 := by
  intro h0
  have hz : spEnd k (Pi.single (Sum.inr i) 1) = 0 := by rw [hkf, h0, zero_smul]
  have hleft : spEnd k⁻¹ (spEnd k (Pi.single (Sum.inr i) 1)) = Pi.single (Sum.inr i) 1 := by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  rw [hz, map_zero] at hleft
  exact (Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : F) ≠ 0)) hleft.symm

theorem fixes_plane_of_perfect
    {K : Subgroup ↥(StatedSp ℓ F)} (hKp : ⁅K, K⁆ = K) {t : Fin ℓ → Fˣ}
    (hKd : K ≤ Subgroup.centralizer
      ({CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ t} : Set ↥(StatedSp ℓ F)))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) 1) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) 1) ∈ stdPlane F ℓ i)
    {i : Fin ℓ} (hti : t i ≠ 1) :
    ∀ k ∈ K, spEnd k (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      spEnd k (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1 := by
  classical
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKp
  intro k hk
  have hke := spEnd_single_inl_eq_smul_of_mem hKd hpl hti hk
  have hkf := spEnd_single_inr_eq_smul_of_mem hKd hpl hti hk
  let χ : ↥K → Fˣ × Fˣ := fun k' =>
    (Units.mk0 ((spEnd (k' : ↥(StatedSp ℓ F)) (Pi.single (Sum.inl i) 1)) (Sum.inl i))
        (spEnd_single_inl_apply_ne_zero
          (spEnd_single_inl_eq_smul_of_mem hKd hpl hti k'.2)),
      Units.mk0 ((spEnd (k' : ↥(StatedSp ℓ F)) (Pi.single (Sum.inr i) 1)) (Sum.inr i))
        (spEnd_single_inr_apply_ne_zero
          (spEnd_single_inr_eq_smul_of_mem hKd hpl hti k'.2)))
  have hmul : ∀ a b : ↥K, χ (a * b) = χ a * χ b := by
    intro a b
    apply Prod.ext
    · apply Units.ext
      have hb' := spEnd_single_inl_eq_smul_of_mem hKd hpl hti b.2
      have ha' := spEnd_single_inl_eq_smul_of_mem hKd hpl hti a.2
      change (spEnd ((a * b : ↥K) : ↥(StatedSp ℓ F)) (Pi.single (Sum.inl i) 1)) (Sum.inl i) =
        (spEnd (a : ↥(StatedSp ℓ F)) (Pi.single (Sum.inl i) 1)) (Sum.inl i) *
          (spEnd (b : ↥(StatedSp ℓ F)) (Pi.single (Sum.inl i) 1)) (Sum.inl i)
      rw [Subgroup.coe_mul, spEnd_mul, Module.End.mul_apply, hb', map_smul, ha']
      simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm]
    · apply Units.ext
      have hb' := spEnd_single_inr_eq_smul_of_mem hKd hpl hti b.2
      have ha' := spEnd_single_inr_eq_smul_of_mem hKd hpl hti a.2
      change (spEnd ((a * b : ↥K) : ↥(StatedSp ℓ F)) (Pi.single (Sum.inr i) 1)) (Sum.inr i) =
        (spEnd (a : ↥(StatedSp ℓ F)) (Pi.single (Sum.inr i) 1)) (Sum.inr i) *
          (spEnd (b : ↥(StatedSp ℓ F)) (Pi.single (Sum.inr i) 1)) (Sum.inr i)
      rw [Subgroup.coe_mul, spEnd_mul, Module.End.mul_apply, hb', map_smul, ha']
      simp [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_comm]
  have hone : χ ⟨k, hk⟩ = 1 :=
    CFSG.CGT.PushingUpLit.CGT6.perfect_map_eq_one χ hmul ⟨k, hk⟩
  constructor
  · have h1 : (spEnd k (Pi.single (Sum.inl i) 1)) (Sum.inl i) = 1 := by
      have := congrArg (fun q : Fˣ × Fˣ => ((q.1 : Fˣ) : F)) hone
      simpa [χ] using this
    rw [hke, h1, one_smul]
  · have h1 : (spEnd k (Pi.single (Sum.inr i) 1)) (Sum.inr i) = 1 := by
      have := congrArg (fun q : Fˣ × Fˣ => ((q.2 : Fˣ) : F)) hone
      simpa [χ] using this
    rw [hkf, h1, one_smul]

private theorem spEnd_diagSp_eq_self_of_mem_stdPlane {s : Fin ℓ → Fˣ} {i : Fin ℓ} (hsi : s i = 1)
    {v : Fin ℓ ⊕ Fin ℓ → F} (hv : v ∈ stdPlane F ℓ i) :
    spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s) v = v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  rw [map_add, map_smul, map_smul, spEnd_diagSp_single_inl, spEnd_diagSp_single_inr]
  simp [hsi]

theorem diagSp_mem_centralizer_of_fixes {K : Subgroup ↥(StatedSp ℓ F)}
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) 1) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) 1) ∈ stdPlane F ℓ i)
    {I : Set (Fin ℓ)}
    (hI : ∀ k ∈ K, ∀ i ∈ I, spEnd k (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 ∧
      spEnd k (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inr i) 1)
    {s : Fin ℓ → Fˣ} (hs : ∀ j ∉ I, s j = 1) :
    CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s ∈
      Subgroup.centralizer (K : Set ↥(StatedSp ℓ F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hcomm : spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s) * spEnd k =
      spEnd k * spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s) := by
    refine (Pi.basisFun F (Fin ℓ ⊕ Fin ℓ)).ext fun b => ?_
    rw [Pi.basisFun_apply]
    rcases b with j | j
    · by_cases hj : j ∈ I
      · rw [Module.End.mul_apply, Module.End.mul_apply, (hI k hk j hj).1,
          spEnd_diagSp_single_inl, map_smul, (hI k hk j hj).1]
      · rw [Module.End.mul_apply, Module.End.mul_apply, spEnd_diagSp_single_inl, hs j hj]
        simp only [Units.val_one, one_smul]
        exact spEnd_diagSp_eq_self_of_mem_stdPlane (hs j hj) (hpl k hk j).1
    · by_cases hj : j ∈ I
      · rw [Module.End.mul_apply, Module.End.mul_apply, (hI k hk j hj).2,
          spEnd_diagSp_single_inr, map_smul, (hI k hk j hj).2]
      · rw [Module.End.mul_apply, Module.End.mul_apply, spEnd_diagSp_single_inr, hs j hj]
        simp only [Units.val_one, inv_one, one_smul]
        exact spEnd_diagSp_eq_self_of_mem_stdPlane (hs j hj) (hpl k hk j).2
  have hcomm' : spEnd k * spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s) =
      spEnd (CFSG.SeitzReduction.SymplecticPilot.diagSp F ℓ s) * spEnd k := hcomm.symm
  apply spLin_injective
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  exact hcomm'

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
