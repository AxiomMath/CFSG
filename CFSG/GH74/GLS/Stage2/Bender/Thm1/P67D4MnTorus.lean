module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRoots
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {L : Type} [Field L]

theorem twistHom_mem_torusGroup_d4 [IsAlgClosed L] (Fr : L →+* L) {x : ModGL TwistTag.D4.tag L}
    (hx : x ∈ torusGroup TwistTag.D4.tag L) :
    twistHom TwistTag.D4 L Fr x ∈ torusGroup TwistTag.D4.tag L := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [twistHom_rootDiagUnit_eq]
  exact rootDiagUnit_mem_torusGroup _

theorem trialityOpposition_twistHom_torus [IsAlgClosed L] (Fr : L →+* L)
    {x : ModGL TwistTag.D4.tag L} (hx : x ∈ torusGroup TwistTag.D4.tag L) :
    trialityOpposition L * twistHom TwistTag.D4 L Fr x * (trialityOpposition L)⁻¹ =
      (twistHom TwistTag.D4 L Fr x)⁻¹ :=
  trialityOpposition_conj_torus (twistHom_mem_torusGroup_d4 Fr hx)

theorem d4Minus_torus_lang [IsAlgClosed L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {e : ModGL TwistTag.D4.tag L} (he : e ∈ torusGroup TwistTag.D4.tag L)
    (hP : diagramMap TwistTag.D4 L * e = e * diagramMap TwistTag.D4 L) :
    ∃ h ∈ torusGroup TwistTag.D4.tag L,
      diagramMap TwistTag.D4 L * h = h * diagramMap TwistTag.D4 L ∧
      h * (trialityOpposition L * twistHom TwistTag.D4 L Fr h * (trialityOpposition L)⁻¹)⁻¹ =
        e := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup he
  rw [diagramMap_mul_rootDiagUnit] at hP
  have hb : (fun i => b (TwistTag.D4.perm.symm i)) = b :=
    rootDiagUnit_injective (mul_right_cancel hP)
  have hb1 : b i0 = b i1 := by
    have := congrFun hb i1
    rwa [perm_symm_i1] at this
  have hb3 : b i1 = b i3 := by
    have := congrFun hb i3
    rwa [perm_symm_i3] at this
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_pow_nat_eq ((b i0 : Lˣ) : L) (Nat.succ_pos q)
  obtain ⟨x2, hx2⟩ := IsAlgClosed.exists_pow_nat_eq ((b i2 : Lˣ) : L) (Nat.succ_pos q)
  have hx0' : x0 ≠ 0 := by
    rintro rfl
    exact (b i0).ne_zero (by rw [← hx0]; simp)
  have hx2' : x2 ≠ 0 := by
    rintro rfl
    exact (b i2).ne_zero (by rw [← hx2]; simp)
  set a0 : Lˣ := Units.mk0 x0 hx0' with ha0
  set a2 : Lˣ := Units.mk0 x2 hx2' with ha2
  have e0 : a0 ^ (q + 1) = b i0 := Units.ext (by simpa [ha0] using hx0)
  have e2 : a2 ^ (q + 1) = b i2 := Units.ext (by simpa [ha2] using hx2)
  set a : Fin TwistTag.D4.tag.rank → Lˣ := d4Tuple a0 a0 a2 a0 with hadef
  have hperm : (fun i => a (TwistTag.D4.perm.symm i)) = a := by
    funext i
    fin_cases i
    · show a i3 = a i0
      rfl
    · show a i0 = a i1
      rfl
    · show a i2 = a i2
      rfl
    · show a i1 = a i3
      rfl
  refine ⟨rootDiagUnit TwistTag.D4.tag a, rootDiagUnit_mem_torusGroup a, ?_, ?_⟩
  · rw [diagramMap_mul_rootDiagUnit, hperm]
  · rw [twistHom_rootDiagUnit_eq]
    rw [trialityOpposition_conj_torus (rootDiagUnit_mem_torusGroup _), inv_inv,
      ← rootDiagUnit_mul]
    congr 1
    funext i
    have h1 : a (TwistTag.D4.perm.symm i) = a i := congrFun hperm i
    have h2 : Units.map Fr.toMonoidHom (a i) = a i ^ q := Units.ext (by simp [hFr])
    show a i * Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i)) = b i
    rw [h1, h2, ← pow_succ']
    fin_cases i
    · exact e0
    · exact e0.trans hb1
    · exact e2
    · exact e0.trans (hb1.trans hb3)

end Torus

end CFSG.GH74.GLS.Stage2.Bender.Thm1
