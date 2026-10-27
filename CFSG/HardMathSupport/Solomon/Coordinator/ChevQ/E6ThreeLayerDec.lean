module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Inndiag

variable {K : Type} [Field K]

theorem exists_mul_rootDiagUnit_of_mem_e6InndiagGL {g : ModGL Tag.E6 K}
    (hg : g ∈ e6InndiagGL K) :
    ∃ x ∈ adjointGroup Tag.E6 K, ∃ b : Fin Tag.E6.rank → Kˣ, g = x * rootDiagUnit Tag.E6 b := by
  rw [mem_e6InndiagGL_iff] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨b, rfl⟩
    · exact ⟨y, hy, 1, by rw [rootDiagUnit_one, mul_one]⟩
    · exact ⟨1, one_mem _, b, by rw [one_mul]; rfl⟩
  | one => exact ⟨1, one_mem _, 1, by rw [rootDiagUnit_one, mul_one]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨x₁, hx₁, b₁, rfl⟩ := hy
    obtain ⟨x₂, hx₂, b₂, rfl⟩ := hz
    refine ⟨x₁ * (rootDiagUnit Tag.E6 b₁ * x₂ * (rootDiagUnit Tag.E6 b₁)⁻¹),
      mul_mem hx₁ (conj_rootDiagUnit_mem_adjointGroup b₁ hx₂), b₁ * b₂, ?_⟩
    rw [rootDiagUnit_mul]
    group
  | inv y _ hy =>
    obtain ⟨x, hx, b, rfl⟩ := hy
    refine ⟨rootDiagUnit Tag.E6 b⁻¹ * x⁻¹ * (rootDiagUnit Tag.E6 b⁻¹)⁻¹,
      conj_rootDiagUnit_mem_adjointGroup b⁻¹ (inv_mem hx), b⁻¹, ?_⟩
    rw [← rootDiagUnit_inv]
    group

end Inndiag

section Transport

variable {G : Type*} [Group G]

theorem map_subgroupOf_eq {C : Subgroup G} {ε : MulAut C} {g : G}
    (hg : ∀ h : C, ((ε h : C) : G) = g * h * g⁻¹) {S T : Subgroup G} (hS : S ≤ C)
    (hST : S.map (MulAut.conj g).toMonoidHom = T) :
    (S.subgroupOf C).map ε.toMonoidHom = T.subgroupOf C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxS : (x : G) ∈ S := hx
    show ((ε x : C) : G) ∈ T
    rw [hg x, ← hST]
    exact ⟨x, hxS, rfl⟩
  · intro hy
    have hy' : (y : G) ∈ T := hy
    rw [← hST] at hy'
    obtain ⟨x, hxS, hxy⟩ := hy'
    refine ⟨⟨x, hS hxS⟩, hxS, ?_⟩
    apply Subtype.ext
    show ((ε ⟨x, hS hxS⟩ : C) : G) = y
    rw [hg]
    simpa [MulAut.conj_apply] using hxy

theorem range_codRestrict_eq {M : Type*} [Group M] {H : Type*} [Group H] (ρ : H →* M)
    (C : Subgroup M) (h : ∀ g, ρ g ∈ C) :
    (ρ.codRestrict C h).range = ρ.range.subgroupOf C := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

end Transport

section Dec

variable
  {K : Type} [Field K] {ω : Kˣ}

theorem exists_shift_pow (j : ℕ) (hj : j < 3) :
    ∃ k : Fin 3, (k = 0 ↔ j = 0) ∧ ∀ i : Fin 3,
      (e6LineFactor K i).map
          (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j)).toMonoidHom =
        e6LineFactor K (i + k) := by
  interval_cases j
  · refine ⟨0, by simp, fun i => ?_⟩
    rw [pow_zero, add_zero]
    ext x
    simp [Subgroup.mem_map, MulAut.conj_apply]
  · refine ⟨1, by decide, fun i => ?_⟩
    rw [pow_one]
    exact e6LineFactor_conj i
  · refine ⟨1 + 1, by decide, fun i => ?_⟩
    rw [pow_two, map_conj_mul_aux, e6LineFactor_conj, e6LineFactor_conj, add_assoc]

theorem map_conj_dec (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {m : ModGL Tag.E6 K}
    (hm : m ∈ toralRootGroup Tag.E6 K (e6LineChar ω)) {j : ℕ} {k : Fin 3}
    (hk : ∀ i : Fin 3, (e6LineFactor K i).map
        (MulAut.conj (canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j)).toMonoidHom =
      e6LineFactor K (i + k)) (b : Fin Tag.E6.rank → Kˣ) (i : Fin 3) :
    (e6LineFactor K i).map (MulAut.conj
        (m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j *
          rootDiagUnit Tag.E6 b)).toMonoidHom = e6LineFactor K (i + k) := by
  have hd : (e6LineFactor K i).map (MulAut.conj (rootDiagUnit Tag.E6 b)).toMonoidHom =
      e6LineFactor K i :=
    map_rootSpan_of_forall fun α hα =>
      map_conj_rootDiagUnit_rootSubgroup b (isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hα))
  rw [map_conj_mul_aux, hd, map_conj_mul_aux, hk]
  exact map_conj_eq_of_mem_normalizer_aux (e6LineFactor_normalizer h3 h1 _ hm)

theorem exists_dec_of_mem [Finite K] (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (hK : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag K) (hsig : MulAut.conj (e6LineElt ω) ∈ E)
    {ε : MulAut (adjointGroup Tag.E6 K)} (hε : ε ∈ E) :
    ∃ (m : ModGL Tag.E6 K) (j : ℕ) (b : Fin Tag.E6.rank → Kˣ),
      m ∈ toralRootGroup Tag.E6 K (e6LineChar ω) ∧ j < 3 ∧
        ∀ h : adjointGroup Tag.E6 K, ((ε h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          (m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j * rootDiagUnit Tag.E6 b) *
            h * (m * canonicalRep (coxeterSystem .E6) K e6LineWeyl ^ j *
              rootDiagUnit Tag.E6 b)⁻¹ := by
  obtain ⟨ĝ, hĝ⟩ : ε ∈ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hEd hε
  set ĥ : ↥(e6InndiagGL K) :=
    ⟨(e6LineElt ω : ModGL Tag.E6 K), adjointGroup_le_e6InndiagGL K (e6LineElt ω).2⟩ with hĥ
  have hσ : e6InndiagConj K ĥ = MulAut.conj (e6LineElt ω) :=
    MulEquiv.ext fun h => Subtype.ext rfl
  have hcomm : ĝ * ĥ = ĥ * ĝ := by
    apply e6InndiagConj_injective K hK
    rw [map_mul, map_mul, hĝ, hσ]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hε⟩ : E) ⟨_, hsig⟩)
  have hcomm' : (ĝ : ModGL Tag.E6 K) * (e6LineElt ω : ModGL Tag.E6 K) =
      (e6LineElt ω : ModGL Tag.E6 K) * ĝ := congrArg Subtype.val hcomm
  obtain ⟨x, hx, b, hxb⟩ := exists_mul_rootDiagUnit_of_mem_e6InndiagGL ĝ.2
  rw [coe_e6LineElt, hxb] at hcomm'
  have hab : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (e6LineChar ω) =
      rootDiagUnit Tag.E6 (e6LineChar ω) * rootDiagUnit Tag.E6 b := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hxc : x * rootDiagUnit Tag.E6 (e6LineChar ω) = rootDiagUnit Tag.E6 (e6LineChar ω) * x := by
    refine mul_right_cancel (b := rootDiagUnit Tag.E6 b) ?_
    calc x * rootDiagUnit Tag.E6 (e6LineChar ω) * rootDiagUnit Tag.E6 b
        = x * (rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (e6LineChar ω)) := by
          rw [mul_assoc, hab]
      _ = x * rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 (e6LineChar ω) := by rw [mul_assoc]
      _ = rootDiagUnit Tag.E6 (e6LineChar ω) * (x * rootDiagUnit Tag.E6 b) := hcomm'
      _ = rootDiagUnit Tag.E6 (e6LineChar ω) * x * rootDiagUnit Tag.E6 b := by rw [mul_assoc]
  have hxcent : x ∈ toralCentralizer Tag.E6 K (e6LineChar ω) :=
    mem_toralCentralizer.2 ⟨hx, mul_inv_eq_iff_eq_mul.2 hxc.symm⟩
  obtain ⟨m, hm, j, hj, hxm⟩ := e6Line_centralizer_mul h3 h1 hxcent
  refine ⟨m, j, b, hm, hj, fun h => ?_⟩
  rw [← hĝ, e6InndiagConj_apply, hxb, hxm]

theorem exists_hdec [Finite K] (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (hK : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag K) (hsig : MulAut.conj (e6LineElt ω) ∈ E)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    (hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K)
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (hd : ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i))
    {ε : MulAut (adjointGroup Tag.E6 K)} (hε : ε ∈ E) :
    ∃ k : Fin 3,
      (∀ i, ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i)).range.map ε.toMonoidHom =
        ((ρ (i + k)).codRestrict (adjointGroup Tag.E6 K) (hρC (i + k))).range) ∧
      (k = 0 → ∀ i, ∃ γ : GL (Fin 3) K, ∀ s,
        ε ((ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) s) =
          (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i) (conjSL γ s)) := by
  obtain ⟨m, j, b, hm, hj, hform⟩ := exists_dec_of_mem h3 h1 hK hE hEd hsig hε
  obtain ⟨k, hk0, hk⟩ := exists_shift_pow (K := K) j hj
  have hle : ∀ i, e6LineFactor K i ≤ adjointGroup Tag.E6 K := fun i x hx => by
    rw [← hrange i] at hx
    obtain ⟨s, rfl⟩ := hx
    exact hρC i s
  refine ⟨k, fun i => ?_, fun hk' i => ?_⟩
  · rw [range_codRestrict_eq, range_codRestrict_eq, hrange, hrange]
    exact map_subgroupOf_eq hform (hle i) (map_conj_dec h3 h1 hm hk b i)
  · have hj0 : j = 0 := hk0.1 hk'
    subst hj0
    simp only [pow_zero, mul_one] at hform
    obtain ⟨γ, hγ⟩ : m * rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i) :=
      mul_mem (toralRootGroup_le_frameActSub h3 h1 hrange hd i hm) (hd i b)
    refine ⟨γ, fun s => Subtype.ext ?_⟩
    rw [hform]
    exact hγ s

end Dec

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
