module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.Action
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.LAWords
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectionF4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.DegZero
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


abbrev V (L : Type) := (Fin Tag.F4.rank → ℤ) → L

section Basic

variable {L : Type} [Field L] [CharP L 2]

theorem eps_eq_one {ε : L} (h : ε * ε = 1) : ε = 1 := by
  rcases mul_self_eq_one_iff.1 h with h | h
  · exact h
  · rw [h]
    exact CharTwo.neg_eq (1 : L)

@[expose] def wF4 : WeylGroup Tag.F4 := TwClass.f4Six.w

@[expose] def nW (L : Type) [Field L] : ModGL Tag.F4 L :=
  canonicalRep (coxeterSystem Tag.F4) L wF4

@[expose] def sigHom (Fr : L →+* L) : ModGL Tag.F4 L →* ModGL Tag.F4 L :=
  (MulAut.conj (nW L)).toMonoidHom.comp (Units.map (entrywiseHom Fr))

theorem sigHom_apply (Fr : L →+* L) (y : ModGL Tag.F4 L) :
    sigHom Fr y = nW L * Units.map (entrywiseHom Fr) y * (nW L)⁻¹ := rfl

theorem map_fr_pinnedX (Fr : L →+* L) (β : Fin Tag.F4.rank → ℤ) (c : L) :
    Units.map (entrywiseHom (τ := Tag.F4) Fr) (pinnedX Tag.F4 L β c) = pinnedX Tag.F4 L β (Fr c) := by
  rw [Units.ext_iff, Units.coe_map]
  show entrywise Fr _ = _
  rw [entrywise_pinnedX]

theorem nW_conj_pinnedX {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (c : L) :
    nW L * pinnedX Tag.F4 L β c * (nW L)⁻¹ = pinnedX Tag.F4 L (wF4 • β) c := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L wF4 hβ
  rw [nW, h, eps_eq_one hε, one_mul]

theorem sigHom_pinnedX (Fr : L →+* L) {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (c : L) :
    sigHom Fr (pinnedX Tag.F4 L β c) = pinnedX Tag.F4 L (wF4 • β) (Fr c) := by
  rw [sigHom_apply, map_fr_pinnedX, nW_conj_pinnedX hβ]

end Basic

section Generic

variable {L : Type} [Field L]

theorem Qθ_map_good {φ : ModGL Tag.F4 L →* ModGL Tag.F4 L} {f : V L → V L}
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hgen : ∀ α ∈ parabolicRadicalRoots Tag.F4 (Jθ Tag.F4), ∀ c : L,
      φ (pinnedX Tag.F4 L α c) ∈ Qθ Tag.F4 L ∧
        heisCoord Tag.F4 L (φ (pinnedX Tag.F4 L α c)) =
          f (heisCoord Tag.F4 L (pinnedX Tag.F4 L α c))) :
    ∀ q ∈ Qθ Tag.F4 L, φ q ∈ Qθ Tag.F4 L ∧
      heisCoord Tag.F4 L (φ q) = f (heisCoord Tag.F4 L q) := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  have hfneg : ∀ a, f (-a) = -f a := fun a => by
    have h := hadd a (-a)
    rw [add_neg_cancel, hf0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  let S : Subgroup (ModGL Tag.F4 L) :=
    { carrier := {q | q ∈ Qθ Tag.F4 L ∧ φ q ∈ Qθ Tag.F4 L ∧
        heisCoord Tag.F4 L (φ q) = f (heisCoord Tag.F4 L q)}
      mul_mem' := by
        rintro q q' ⟨hq, hφq, hqe⟩ ⟨hq', hφq', hq'e⟩
        refine ⟨mul_mem hq hq', by rw [map_mul]; exact mul_mem hφq hφq', ?_⟩
        rw [map_mul, (heisCoord_spec Tag.F4 L).mul _ hφq _ hφq', hqe, hq'e,
          (heisCoord_spec Tag.F4 L).mul _ hq _ hq', hadd]
      one_mem' := ⟨one_mem _, by rw [map_one]; exact one_mem _, by
        rw [map_one, heisCoord_one, hf0]⟩
      inv_mem' := by
        rintro q ⟨hq, hφq, hqe⟩
        refine ⟨inv_mem hq, by rw [map_inv]; exact inv_mem hφq, ?_⟩
        rw [map_inv, heisCoord_inv hφq, hqe, heisCoord_inv hq, hfneg] }
  have hle : Qθ Tag.F4 L ≤ S := by
    show rootSpan Tag.F4 L (parabolicRadicalRoots Tag.F4 (Jθ Tag.F4)) ≤ S
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
    exact ⟨pinnedX_mem_rootSpan hα z, hgen α hα z⟩
  intro q hq
  exact (hle hq).2

end Generic

section Compat

variable {L : Type} [Field L] [CharP L 2]

theorem w_smul_deg1 : ∀ β ∈ rootFinset Tag.F4, β 0 = 1 → wF4 • β ∈ rootFinset Tag.F4 ∧
    (wF4 • β) 0 = 1 := by
  intro β hβ h1
  have e : wF4 • β = TwClass.wordF4.foldr (reflect Tag.F4) β :=
    wordProd_smul_eq_foldr Tag.F4 TwClass.wordF4 β
  rw [e]
  revert β
  decide +kernel


theorem w_smul_theta : wF4 • highRoot Tag.F4 = highRoot Tag.F4 := by
  have e : wF4 • highRoot Tag.F4 = TwClass.wordF4.foldr (reflect Tag.F4) (highRoot Tag.F4) :=
    wordProd_smul_eq_foldr Tag.F4 TwClass.wordF4 _
  rw [e]
  decide +kernel

theorem fr_Qθ (Fr : L →+* L) : ∀ q ∈ Qθ Tag.F4 L,
    Units.map (entrywiseHom (τ := Tag.F4) Fr) q ∈ Qθ Tag.F4 L ∧
      heisCoord Tag.F4 L (Units.map (entrywiseHom (τ := Tag.F4) Fr) q) =
        fun ν => Fr (heisCoord Tag.F4 L q ν) := by
  refine Qθ_map_good (φ := Units.map (entrywiseHom (τ := Tag.F4) Fr))
    (f := fun v ν => Fr (v ν)) (fun a b => by funext ν; simp) ?_
  intro α hα c
  rw [map_fr_pinnedX]
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 h _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_deg1 α h, (heisCoord_spec Tag.F4 L).pinnedX_deg1 α h]
    funext ν
    by_cases hν : ν = α <;> simp [Pi.single_apply, hν]
  · subst h
    refine ⟨pinnedX_mem_rootSpan hα _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_highRoot, (heisCoord_spec Tag.F4 L).pinnedX_highRoot]
    funext ν
    simp

theorem nW_Qθ : ∀ q ∈ Qθ Tag.F4 L, nW L * q * (nW L)⁻¹ ∈ Qθ Tag.F4 L ∧
    heisCoord Tag.F4 L (nW L * q * (nW L)⁻¹) = fun ν => heisCoord Tag.F4 L q (wF4⁻¹ • ν) := by
  refine Qθ_map_good (φ := (MulAut.conj (nW L)).toMonoidHom)
    (f := fun v ν => v (wF4⁻¹ • ν)) (fun a b => by funext ν; simp) ?_
  intro α hα c
  have hαr : IsRoot Tag.F4 α := by
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
    · exact h.1
    · subst h; exact isRoot_highRoot _
  have e : (MulAut.conj (nW L)).toMonoidHom (pinnedX Tag.F4 L α c) =
      pinnedX Tag.F4 L (wF4 • α) c := nW_conj_pinnedX hαr c
  rw [e]
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · obtain ⟨hr, hd⟩ := w_smul_deg1 α (mem_rootFinset.2 hαr) h.2
    have hD : wF4 • α ∈ Deg1 Tag.F4 := ⟨mem_rootFinset.1 hr, hd⟩
    refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hD _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_deg1 _ hD, (heisCoord_spec Tag.F4 L).pinnedX_deg1 α h]
    funext ν
    by_cases hν : ν = wF4 • α
    · subst hν
      simp
    · have : wF4⁻¹ • ν ≠ α := fun e => hν (by rw [← e, smul_inv_smul])
      simp [Pi.single_apply, hν, this]
  · subst h
    rw [w_smul_theta]
    refine ⟨pinnedX_mem_rootSpan hα _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_highRoot]
    funext ν
    simp [(heisCoord_spec Tag.F4 L).pinnedX_highRoot]

theorem sig_Qθ (Fr : L →+* L) : ∀ q ∈ Qθ Tag.F4 L, sigHom Fr q ∈ Qθ Tag.F4 L ∧
    heisCoord Tag.F4 L (sigHom Fr q) = fun ν => Fr (heisCoord Tag.F4 L q (wF4⁻¹ • ν)) := by
  intro q hq
  obtain ⟨h1, h2⟩ := fr_Qθ Fr q hq
  obtain ⟨h3, h4⟩ := nW_Qθ _ h1
  refine ⟨h3, ?_⟩
  rw [sigHom_apply, h4, h2]


end Compat

section IsW

variable {L : Type} [Field L] [CharP L 2] (Fr : L →+* L) (H : Subgroup (ModGL Tag.F4 L))

@[expose] def IsW (v : V L) : Prop :=
  ∃ q ∈ H, q ∈ Qθ Tag.F4 L ∧ sigHom Fr q = q ∧ heisCoord Tag.F4 L q = v

variable {Fr H}

theorem isW_zero : IsW Fr H (0 : V L) :=
  ⟨1, one_mem _, one_mem _, map_one _, heisCoord_one⟩

theorem IsW.add {v v' : V L} (h : IsW Fr H v) (h' : IsW Fr H v') : IsW Fr H (v + v') := by
  obtain ⟨q, hqH, hq, hs, rfl⟩ := h
  obtain ⟨q', hq'H, hq', hs', rfl⟩ := h'
  exact ⟨q * q', mul_mem hqH hq'H, mul_mem hq hq', by rw [map_mul, hs, hs'],
    (heisCoord_spec Tag.F4 L).mul q hq q' hq'⟩

theorem IsW.neg {v : V L} (h : IsW Fr H v) : IsW Fr H (-v) := by
  obtain ⟨q, hqH, hq, hs, rfl⟩ := h
  exact ⟨q⁻¹, inv_mem hqH, inv_mem hq, by rw [map_inv, hs], heisCoord_inv hq⟩

theorem IsW.supp {v : V L} (h : IsW Fr H v) {ν : Fin Tag.F4.rank → ℤ} (hν : ν ∉ Deg1 Tag.F4) :
    v ν = 0 := by
  obtain ⟨q, -, hq, -, rfl⟩ := h
  exact (heisCoord_spec Tag.F4 L).support q hq ν hν

theorem IsW.sf {v : V L} (h : IsW Fr H v) (ν : Fin Tag.F4.rank → ℤ) :
    v ν = Fr (v (wF4⁻¹ • ν)) := by
  obtain ⟨q, -, hq, hs, rfl⟩ := h
  have h1 := (sig_Qθ Fr q hq).2
  rw [hs] at h1
  exact congrFun h1 ν

@[expose] def HasAct (y : ModGL Tag.F4 L) (A : V L → V L) : Prop :=
  ∀ q ∈ Qθ Tag.F4 L, y * q * y⁻¹ ∈ Qθ Tag.F4 L ∧
    heisCoord Tag.F4 L (y * q * y⁻¹) = A (heisCoord Tag.F4 L q)

theorem HasAct.mul {y y' : ModGL Tag.F4 L} {A A' : V L → V L} (h : HasAct y A) (h' : HasAct y' A') :
    HasAct (y * y') (A ∘ A') := by
  intro q hq
  obtain ⟨h1, h2⟩ := h' q hq
  obtain ⟨h3, h4⟩ := h _ h1
  have e : y * y' * q * (y * y')⁻¹ = y * (y' * q * y'⁻¹) * y⁻¹ := by group
  rw [e]
  exact ⟨h3, by rw [h4, h2]; rfl⟩

theorem IsW.act {y : ModGL Tag.F4 L} {A : V L → V L} {v : V L} (hyH : y ∈ H)
    (hys : sigHom Fr y = y) (hA : HasAct y A) (hv : IsW Fr H v) : IsW Fr H (A v) := by
  obtain ⟨q, hqH, hq, hs, rfl⟩ := hv
  obtain ⟨h1, h2⟩ := hA q hq
  refine ⟨y * q * y⁻¹, mul_mem (mul_mem hyH hqH) (inv_mem hyH), h1, ?_, h2⟩
  rw [map_mul, map_mul, map_inv, hs, hys]

end IsW

section Act

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

structure ActData (L : Type) [Field L] where
  a1 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ
  a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ
  adm1 : Adm1 a1
  adm2 : Adm2 a2
  hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : L,
    HasAct (pinnedX Tag.F4 L γ t) (actFun a1 a2 γ t)

theorem exists_actData (L : Type) [Field L] : Nonempty (ActData L) := by
  obtain ⟨a1, a2, h1, h2, h⟩ := exists_action_data L
  refine ⟨⟨a1, a2, h1, h2, fun γ hγ hγ0 t q hq => ?_⟩⟩
  have hL : pinnedX Tag.F4 L γ t ∈ Lθ Tag.F4 L :=
    pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hγ) hγ0 t
  exact ⟨Lθ_conj_mem_Qθ hL hq, h γ hγ hγ0 t q hq⟩

end Act


section Roots

@[expose] def rS : Fin Tag.F4.rank → ℤ := ![1, 0, 0, 0]
@[expose] def rA1 : Fin Tag.F4.rank → ℤ := ![1, 1, 0, 0]
@[expose] def rA2 : Fin Tag.F4.rank → ℤ := ![1, 1, 2, 0]
@[expose] def rA3 : Fin Tag.F4.rank → ℤ := ![1, 1, 2, 2]
@[expose] def rB12 : Fin Tag.F4.rank → ℤ := ![1, 1, 1, 0]
@[expose] def rB13 : Fin Tag.F4.rank → ℤ := ![1, 1, 1, 1]
@[expose] def rB23 : Fin Tag.F4.rank → ℤ := ![1, 1, 2, 1]
@[expose] def a3 : Fin Tag.F4.rank → ℤ := ![0, 0, 1, 0]
@[expose] def a4 : Fin Tag.F4.rank → ℤ := ![0, 0, 0, 1]
@[expose] def g5 : Fin Tag.F4.rank → ℤ := ![0, 0, 1, 1]
@[expose] def g5n : Fin Tag.F4.rank → ℤ := ![0, 0, -1, -1]

theorem rS_root : rS ∈ rootFinset Tag.F4 := by decide +kernel
theorem rA1_root : rA1 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rA2_root : rA2 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rA3_root : rA3 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rB12_root : rB12 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rB13_root : rB13 ∈ rootFinset Tag.F4 := by decide +kernel
theorem rB23_root : rB23 ∈ rootFinset Tag.F4 := by decide +kernel
theorem a3_root : a3 ∈ rootFinset Tag.F4 := by decide +kernel
theorem a4_root : a4 ∈ rootFinset Tag.F4 := by decide +kernel
theorem g5_root : g5 ∈ rootFinset Tag.F4 := by decide +kernel
theorem g5n_root : g5n ∈ rootFinset Tag.F4 := by decide +kernel
theorem rS_deg : rS 0 = 1 := by decide
theorem rA1_deg : rA1 0 = 1 := by decide
theorem rA2_deg : rA2 0 = 1 := by decide
theorem rA3_deg : rA3 0 = 1 := by decide
theorem rB12_deg : rB12 0 = 1 := by decide
theorem rB13_deg : rB13 0 = 1 := by decide
theorem rB23_deg : rB23 0 = 1 := by decide
theorem a3_deg : a3 0 = 0 := by decide
theorem a4_deg : a4 0 = 0 := by decide
theorem g5_deg : g5 0 = 0 := by decide
theorem g5n_deg : g5n 0 = 0 := by decide

end Roots

section Coord

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

variable {L : Type} [Field L] [CharP L 2]

@[expose] def Supp (v : V L) : Prop := ∀ ν, ν ∉ Deg1 Tag.F4 → v ν = 0

theorem supp_zero {v : V L} (hv : Supp v) {X : Fin Tag.F4.rank → ℤ} (hX : X ∉ rootFinset Tag.F4) :
    v X = 0 := hv X (fun h => hX (mem_rootFinset.2 h.1))

theorem cast_one_of_abs {z : ℤ} (h : |z| = 1) : (z : L) = 1 := by
  rcases (abs_eq zero_le_one).1 h with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

theorem cast_zero_of_abs {z : ℤ} (h : |z| = 2) : (z : L) = 0 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 h with rfl | rfl
  · simp [CharTwo.two_eq_zero]
  · simp [CharTwo.two_eq_zero]

theorem mem_deg1Roots {β : Fin Tag.F4.rank → ℤ} (h : β ∈ Deg1 Tag.F4) :
    β ∈ DetectF4.deg1Roots := by
  have := DetectF4.deg_one_roots β (mem_rootFinset.2 h.1) h.2
  unfold DetectF4.deg1Roots
  rcases this with h | h
  · exact List.mem_append_left _ h.1
  · exact List.mem_append_right _ h.1

variable (AD : ActData L)

theorem act_coord {v : V L} (hv : Supp v) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ rootFinset Tag.F4) (hγ0 : γ 0 = 0) (t : L) {ν : Fin Tag.F4.rank → ℤ}
    (hν : ν ∈ rootFinset Tag.F4) (hν1 : ν 0 = 1) :
    DetectF4.actFun AD.a1 AD.a2 γ t v ν = v ν +
      t * (if ν - 2 • γ ∈ rootFinset Tag.F4 then 0 else 1) * v (ν - γ) + t ^ 2 * v (ν - 2 • γ) := by
  unfold DetectF4.actFun
  have hA1 : (AD.a1 γ (ν - γ) : L) * v (ν - γ) =
      (if ν - 2 • γ ∈ rootFinset Tag.F4 then 0 else 1) * v (ν - γ) := by
    by_cases h : ν - γ ∈ Deg1 Tag.F4
    · have hsum : γ + (ν - γ) ∈ rootFinset Tag.F4 := by rwa [add_sub_cancel]
      have h1 := (AD.adm1 γ hγ hγ0 _ (mem_deg1Roots h)).1 hsum
      have e : ν - γ - γ = ν - 2 • γ := by rw [sub_sub, two_smul]
      rw [e] at h1
      by_cases hm : ν - 2 • γ ∈ rootFinset Tag.F4
      · rw [if_pos hm] at h1
        rw [if_pos hm, cast_zero_of_abs h1]
      · rw [if_neg hm] at h1
        rw [if_neg hm, cast_one_of_abs h1]
    · rw [hv _ h]
      simp
  have hA2 : (AD.a2 γ (ν - 2 • γ) : L) * v (ν - 2 • γ) = v (ν - 2 • γ) := by
    by_cases h : ν - 2 • γ ∈ Deg1 Tag.F4
    · have hsum : 2 • γ + (ν - 2 • γ) ∈ rootFinset Tag.F4 := by rwa [add_sub_cancel]
      have h1 := (AD.adm2 γ hγ hγ0 _ (mem_deg1Roots h)).1 hsum
      rw [cast_one_of_abs h1, one_mul]
    · rw [hv _ h]
      simp
  calc v ν + t * (AD.a1 γ (ν - γ) : L) * v (ν - γ) + t ^ 2 * (AD.a2 γ (ν - 2 • γ) : L) *
        v (ν - 2 • γ)
      = v ν + t * ((AD.a1 γ (ν - γ) : L) * v (ν - γ)) +
        t ^ 2 * ((AD.a2 γ (ν - 2 • γ) : L) * v (ν - 2 • γ)) := by ring
    _ = _ := by rw [hA1, hA2]; ring

theorem Supp.act {v : V L} (hv : Supp v) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ rootFinset Tag.F4) (hγ0 : γ 0 = 0) (t : L) :
    Supp (DetectF4.actFun AD.a1 AD.a2 γ t v) := by
  intro ν hν
  unfold DetectF4.actFun
  rw [hv ν hν]
  have hA1 : (AD.a1 γ (ν - γ) : L) * v (ν - γ) = 0 := by
    by_cases h : ν - γ ∈ Deg1 Tag.F4
    · have hν0 : ν 0 = 1 := by
        have : (ν - γ) 0 = 1 := h.2
        simpa [Pi.sub_apply, hγ0] using this
      have hνn : ν ∉ rootFinset Tag.F4 := fun hr => hν ⟨mem_rootFinset.1 hr, hν0⟩
      have h0 : AD.a1 γ (ν - γ) = 0 :=
        (AD.adm1 γ hγ hγ0 _ (mem_deg1Roots h)).2 (by rwa [add_sub_cancel])
      rw [h0]
      simp
    · rw [hv _ h]
      simp
  have hA2 : (AD.a2 γ (ν - 2 • γ) : L) * v (ν - 2 • γ) = 0 := by
    by_cases h : ν - 2 • γ ∈ Deg1 Tag.F4
    · have hν0 : ν 0 = 1 := by
        have : (ν - 2 • γ) 0 = 1 := h.2
        simpa [Pi.sub_apply, hγ0] using this
      have hνn : ν ∉ rootFinset Tag.F4 := fun hr => hν ⟨mem_rootFinset.1 hr, hν0⟩
      have h0 : AD.a2 γ (ν - 2 • γ) = 0 :=
        (AD.adm2 γ hγ hγ0 _ (mem_deg1Roots h)).2 (by rwa [add_sub_cancel])
      rw [h0]
      simp
    · rw [hv _ h]
      simp
  calc 0 + t * (AD.a1 γ (ν - γ) : L) * v (ν - γ) + t ^ 2 * (AD.a2 γ (ν - 2 • γ) : L) *
        v (ν - 2 • γ)
      = t * ((AD.a1 γ (ν - γ) : L) * v (ν - γ)) +
        t ^ 2 * ((AD.a2 γ (ν - 2 • γ) : L) * v (ν - 2 • γ)) := by ring
    _ = 0 := by rw [hA1, hA2]; ring

theorem actc_g5_rS {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rS =
      v rS := by
  rw [act_coord AD hv g5_root g5_deg t rS_root rS_deg]
  have z1 : v (rS - g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rS - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rS - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5_rA1 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rA1 =
      v rA1 := by
  rw [act_coord AD hv g5_root g5_deg t rA1_root rA1_deg]
  have z1 : v (rA1 - g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA1 - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA1 - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5_rA2 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rA2 =
      v rA2 := by
  rw [act_coord AD hv g5_root g5_deg t rA2_root rA2_deg]
  have z1 : v (rA2 - g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA2 - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA2 - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5_rA3 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rA3 =
      v rA3 + t ^ 2 * v rA1 := by
  rw [act_coord AD hv g5_root g5_deg t rA3_root rA3_deg]
  have e1 : rA3 - g5 = rB13 := by decide
  rw [e1]
  have e2 : rA3 - 2 • g5 = rA1 := by decide
  rw [e2, if_pos (by decide +kernel : rA1 ∈ rootFinset Tag.F4)]
  ring

theorem actc_g5_rB12 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rB12 =
      v rB12 := by
  rw [act_coord AD hv g5_root g5_deg t rB12_root rB12_deg]
  have z1 : v (rB12 - g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rB12 - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB12 - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5_rB13 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rB13 =
      v rB13 + t * v rA1 := by
  rw [act_coord AD hv g5_root g5_deg t rB13_root rB13_deg]
  have e1 : rB13 - g5 = rA1 := by decide
  rw [e1]
  have z2 : v (rB13 - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB13 - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5_rB23 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5 t v rB23 =
      v rB23 + t * v rB12 := by
  rw [act_coord AD hv g5_root g5_deg t rB23_root rB23_deg]
  have e1 : rB23 - g5 = rB12 := by decide
  rw [e1]
  have z2 : v (rB23 - 2 • g5) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB23 - 2 • g5 ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rS {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rS =
      v rS := by
  rw [act_coord AD hv g5n_root g5n_deg t rS_root rS_deg]
  have z1 : v (rS - g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rS - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rS - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rA1 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rA1 =
      v rA1 + t ^ 2 * v rA3 := by
  rw [act_coord AD hv g5n_root g5n_deg t rA1_root rA1_deg]
  have e1 : rA1 - g5n = rB13 := by decide
  rw [e1]
  have e2 : rA1 - 2 • g5n = rA3 := by decide
  rw [e2, if_pos (by decide +kernel : rA3 ∈ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rA2 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rA2 =
      v rA2 := by
  rw [act_coord AD hv g5n_root g5n_deg t rA2_root rA2_deg]
  have z1 : v (rA2 - g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA2 - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA2 - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rA3 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rA3 =
      v rA3 := by
  rw [act_coord AD hv g5n_root g5n_deg t rA3_root rA3_deg]
  have z1 : v (rA3 - g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA3 - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA3 - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rB12 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rB12 =
      v rB12 + t * v rB23 := by
  rw [act_coord AD hv g5n_root g5n_deg t rB12_root rB12_deg]
  have e1 : rB12 - g5n = rB23 := by decide
  rw [e1]
  have z2 : v (rB12 - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB12 - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rB13 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rB13 =
      v rB13 + t * v rA3 := by
  rw [act_coord AD hv g5n_root g5n_deg t rB13_root rB13_deg]
  have e1 : rB13 - g5n = rA3 := by decide
  rw [e1]
  have z2 : v (rB13 - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB13 - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_g5n_rB23 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 g5n t v rB23 =
      v rB23 := by
  rw [act_coord AD hv g5n_root g5n_deg t rB23_root rB23_deg]
  have z1 : v (rB23 - g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rB23 - 2 • g5n) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB23 - 2 • g5n ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rS {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rS =
      v rS := by
  rw [act_coord AD hv a3_root a3_deg t rS_root rS_deg]
  have z1 : v (rS - a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rS - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rS - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rA1 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rA1 =
      v rA1 := by
  rw [act_coord AD hv a3_root a3_deg t rA1_root rA1_deg]
  have z1 : v (rA1 - a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA1 - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA1 - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rA2 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rA2 =
      v rA2 + t ^ 2 * v rA1 := by
  rw [act_coord AD hv a3_root a3_deg t rA2_root rA2_deg]
  have e1 : rA2 - a3 = rB12 := by decide
  rw [e1]
  have e2 : rA2 - 2 • a3 = rA1 := by decide
  rw [e2, if_pos (by decide +kernel : rA1 ∈ rootFinset Tag.F4)]
  ring

theorem actc_a3_rA3 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rA3 =
      v rA3 := by
  rw [act_coord AD hv a3_root a3_deg t rA3_root rA3_deg]
  have z1 : v (rA3 - a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA3 - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA3 - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rB12 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rB12 =
      v rB12 + t * v rA1 := by
  rw [act_coord AD hv a3_root a3_deg t rB12_root rB12_deg]
  have e1 : rB12 - a3 = rA1 := by decide
  rw [e1]
  have z2 : v (rB12 - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB12 - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rB13 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rB13 =
      v rB13 := by
  rw [act_coord AD hv a3_root a3_deg t rB13_root rB13_deg]
  have z1 : v (rB13 - a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rB13 - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB13 - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a3_rB23 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a3 t v rB23 =
      v rB23 + t * v rB13 := by
  rw [act_coord AD hv a3_root a3_deg t rB23_root rB23_deg]
  have e1 : rB23 - a3 = rB13 := by decide
  rw [e1]
  have z2 : v (rB23 - 2 • a3) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB23 - 2 • a3 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rS {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rS =
      v rS := by
  rw [act_coord AD hv a4_root a4_deg t rS_root rS_deg]
  have z1 : v (rS - a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rS - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rS - 2 • a4 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rA1 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rA1 =
      v rA1 := by
  rw [act_coord AD hv a4_root a4_deg t rA1_root rA1_deg]
  have z1 : v (rA1 - a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA1 - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA1 - 2 • a4 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rA2 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rA2 =
      v rA2 := by
  rw [act_coord AD hv a4_root a4_deg t rA2_root rA2_deg]
  have z1 : v (rA2 - a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rA2 - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rA2 - 2 • a4 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rA3 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rA3 =
      v rA3 + t ^ 2 * v rA2 := by
  rw [act_coord AD hv a4_root a4_deg t rA3_root rA3_deg]
  have e1 : rA3 - a4 = rB23 := by decide
  rw [e1]
  have e2 : rA3 - 2 • a4 = rA2 := by decide
  rw [e2, if_pos (by decide +kernel : rA2 ∈ rootFinset Tag.F4)]
  ring

theorem actc_a4_rB12 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rB12 =
      v rB12 := by
  rw [act_coord AD hv a4_root a4_deg t rB12_root rB12_deg]
  have z1 : v (rB12 - a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z1]
  have z2 : v (rB12 - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB12 - 2 • a4 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rB13 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rB13 =
      v rB13 + t * v rB12 := by
  rw [act_coord AD hv a4_root a4_deg t rB13_root rB13_deg]
  have e1 : rB13 - a4 = rB12 := by decide
  rw [e1]
  have z2 : v (rB13 - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB13 - 2 • a4 ∉ rootFinset Tag.F4)]
  ring

theorem actc_a4_rB23 {v : V L} (hv : Supp v) (t : L) :
    actFun AD.a1 AD.a2 a4 t v rB23 =
      v rB23 + t * v rA2 := by
  rw [act_coord AD hv a4_root a4_deg t rB23_root rB23_deg]
  have e1 : rB23 - a4 = rA2 := by decide
  rw [e1]
  have z2 : v (rB23 - 2 • a4) = 0 := supp_zero hv (by decide +kernel)
  rw [z2, if_neg (by decide +kernel : rB23 - 2 • a4 ∉ rootFinset Tag.F4)]
  ring


end Coord

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
