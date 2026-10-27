module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldReduce
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VExpOut
public import CFSG.HardMathSupport.Solomon.Coordinator.PSL2CentDefs
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (GLAPComponent GLAPPrimeCore GLAPLayer StatedProj StatedSL)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.LocalAnalysis.GLTheoremB

theorem l514vexp_centSolvable (hC : PSL2CentSolvable) {F : Type} [Field F] [Finite F]
    {c : StatedProj (StatedSL 2 F)} (hc : c ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({c} : Set (StatedProj (StatedSL 2 F)))) := by
  let φ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hc' : φ.symm c ≠ 1 := fun h => hc (by simpa using congrArg φ h)
  have : Group.IsSolvable ↥(Subgroup.centralizer
      ({φ.symm c} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) := hC F (φ.symm c) hc'
  let f : ↥(Subgroup.centralizer ({c} : Set (StatedProj (StatedSL 2 F)))) →*
      ↥(Subgroup.centralizer ({φ.symm c} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :=
    ((φ.symm.toMonoidHom).comp (Subgroup.subtype _)).codRestrict _ (fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 x.2
      change φ.symm (x : StatedProj (StatedSL 2 F)) * φ.symm c = φ.symm c * φ.symm x
      rw [← map_mul, ← map_mul, this])
  exact Group.isSolvable_of_isSolvable_injective (f := f) (fun x y h =>
    Subtype.ext (φ.symm.injective (congrArg Subtype.val h)))

theorem l514vexp_pow_apply_of_fix {Q : Type} [Group Q] {a : MulAut Q} {x : Q} (hx : a x = x) (n : ℕ) :
    (a ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem l514vexp_inner_of_descend {Q M : Type} [Group Q] [Group M] [Group.IsPerfect Q]
    (e : (Q ⧸ Subgroup.center Q) ≃* M) {τ : MulAut Q} {c : M}
    (h : MulAut.congr e (centerDescend Q τ) = MulAut.conj c) : ∃ y : Q, MulAut.conj y = τ := by
  have h1 : centerDescend Q τ = MulAut.conj (e.symm c) := by
    apply (MulAut.congr e).injective
    rw [h, congr_mulAutConj, MulEquiv.apply_symm_apply]
  exact isInnerAut_of_isInnerAut_centerDescend ⟨e.symm c, h1.symm⟩

theorem l2exp_core (hU : L2OrderUnique) (h1 : L2Aut3Classification) (h2 : L2FieldFixed)
    (h0 : L2CentreThree) (hC : PSL2CentSolvable) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hO : GLAPPrimeCore 3 Q = ⊥) {s r0 : ℕ} (hs : IsTypeL2 s Q)
    {a b : MulAut Q} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hnot : ∀ y : Q, MulAut.conj y ≠ a)
    {S : Subgroup Q} (hS : GLAPComponent 3 (fixSub a ⊓ fixSub b) S) (hr : IsTypeL2 r0 (barOf 3 S)) :
    s = r0 ^ 3 ∨ ((r0 = 4 ∨ r0 = 5) ∧ (s = 64 ∨ s = 125)) := by
  have hperf : Group.IsPerfect Q := ⟨hQ.1⟩
  have hSsolv : Group.IsSolvable ↥S → False := fun hsv => by
    have hb : Group.IsSolvable (barOf 3 S) := inferInstanceAs (Group.IsSolvable (↥S ⧸ _))
    exact false_of_quasisimple_of_solvable (isQuasisimple_quotient_of_glaPComponent hS) hb
  obtain ⟨F, hFf, hFfin, hcF, ⟨e⟩⟩ := hs
  have hs : IsTypeL2 s Q := ⟨F, hFf, hFfin, hcF, ⟨e⟩⟩
  have hα3 : MulAut.congr e (centerDescend Q a) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ha3, map_one, map_one]
  have hβ3 : MulAut.congr e (centerDescend Q b) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hb3, map_one, map_one]
  have hαβ : MulAut.congr e (centerDescend Q a) * MulAut.congr e (centerDescend Q b) =
      MulAut.congr e (centerDescend Q b) * MulAut.congr e (centerDescend Q a) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hab]
  rcases l514vexp_out3 F _ _ hα3 hβ3 hαβ with ⟨c, hc⟩ | ⟨j, c, hc⟩
  · exfalso
    obtain ⟨y, hy⟩ := l514vexp_inner_of_descend e hc.symm
    exact hnot y hy
  · have hb'' : MulAut.congr e (centerDescend Q (b * a ^ j)) = MulAut.conj c := by
      rw [map_mul, map_mul, map_pow, map_pow, hc]
    obtain ⟨q, hq⟩ := l514vexp_inner_of_descend e hb''.symm.symm
    have hfix : ∀ x : Q, a x = x → (b * a ^ j) x = b x := fun x hx => by
      rw [MulAut.mul_apply, l514vexp_pow_apply_of_fix hx]
    by_cases hq1 : MulAut.conj q = 1
    · have hba : fixSub a ⊓ fixSub b = fixSub a := by
        apply le_antisymm inf_le_left
        intro x hx
        refine ⟨hx, ?_⟩
        have h3 := hfix x hx
        rw [← hq, hq1] at h3
        show b x = x
        simpa using h3.symm
      rw [hba] at hS
      rcases l2fld_core hU h1 h2 h0 hQ hO hs ha3 hS hr with ⟨h, -⟩ | ⟨-, -, hc⟩
      · exact absurd (by rw [h]; exact map_one _) (hnot 1)
      · exact hc
    · exfalso
      have hqz : (q : Q ⧸ Subgroup.center Q) ≠ 1 := fun h => hq1 (by
        have hz : q ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 h
        ext x
        rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_center_iff.1 hz x).symm)
      have hc0 : e (q : Q ⧸ Subgroup.center Q) ≠ 1 := fun h => hqz (e.map_eq_one_iff.1 h)
      have hsol := l514vexp_centSolvable hC hc0
      have hcomm : ∀ x : ↥S, e (QuotientGroup.mk (x : Q)) * e (q : Q ⧸ Subgroup.center Q) =
          e (q : Q ⧸ Subgroup.center Q) * e (QuotientGroup.mk (x : Q)) := fun x => by
        have hx : (x : Q) ∈ fixSub a ⊓ fixSub b := hS.1 x.2
        have h3 : (MulAut.conj q) (x : Q) = x := by
          rw [hq, MulAut.mul_apply, l514vexp_pow_apply_of_fix hx.1]
          exact hx.2
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h3
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h3]
      let f : ↥S →* ↥(Subgroup.centralizer ({e (q : Q ⧸ Subgroup.center Q)} :
          Set (StatedProj (StatedSL 2 F)))) :=
        { toFun := fun x => ⟨e (QuotientGroup.mk (x : Q)),
            Subgroup.mem_centralizer_singleton_iff.2 (hcomm x)⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun x y => Subtype.ext (by simp) }
      have := hsol
      refine hSsolv (CFSG.Quasithin.isSolvable_of_ker_le_center f ?_)
      intro y hy
      have h1' : e (QuotientGroup.mk (y : Q)) = 1 := congrArg Subtype.val hy
      have h2' : (QuotientGroup.mk (y : Q) : Q ⧸ Subgroup.center Q) = 1 := e.map_eq_one_iff.1 h1'
      have h3' : (y : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 h2'
      rw [Subgroup.mem_center_iff] at h3' ⊢
      intro w
      exact Subtype.ext (h3' (w : Q))

end CFSG.HardMathSupport.Solomon.Coordinator
