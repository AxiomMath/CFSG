module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
import CFSG.Walter.Bender1970.S2.Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p', hp'⟩ := CharP.exists F
  have hp'prime : p'.Prime := CharP.char_is_prime F p'
  obtain ⟨m, -, hcard⟩ := FiniteField.card F p'
  have hdvd : p' ∣ 2 ^ n := by
    rw [← hF, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p' m.pos.ne'
  have h2 : p' ∣ 2 := hp'prime.dvd_of_dvd_pow hdvd
  have : p' = 2 := (Nat.prime_dvd_prime_iff_eq hp'prime Nat.prime_two).mp h2
  subst this
  exact hp'

private theorem psi_range_top {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)}
    {ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S}
    (hqs : CFSG.Open.IsQuasisimple ↥S) (hψ : GLifts θ ψ) : ψ.range = ⊤ := by
  have hsurj : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) :=
    QuotientGroup.mk'_surjective
      (N := (LargeEvenScalars (Fin d) F).subgroupOf (LargeEvenSLGroup (Fin d) F))
  have hle : (⊤ : Subgroup ↥S) ≤ ψ.range ⊔ Subgroup.center ↥S := by
    intro s _
    obtain ⟨u, hu⟩ := hsurj (θ (QuotientGroup.mk' (Subgroup.center ↥S) s))
    have hEq : QuotientGroup.mk' (Subgroup.center ↥S) (ψ u) =
        QuotientGroup.mk' (Subgroup.center ↥S) s := by
      apply θ.injective
      have hψu' : θ (QuotientGroup.mk' (Subgroup.center ↥S) (ψ u)) =
          LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) u := hψ u
      rw [hψu']
      exact hu
    obtain ⟨z, hz, hzs⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center ↥S)).mp hEq
    exact (Subgroup.mem_sup_of_normal_right (s := ψ.range)
      (t := Subgroup.center ↥S)).mpr ⟨ψ u, ⟨u, rfl⟩, z, hz, hzs⟩
  exact CFSG.Walter.eq_top_of_sup_center_eq_top hqs.1 (eq_top_iff.mpr hle)

private theorem psi_ker_le_center {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)}
    {ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S} (hψ : GLifts θ ψ) :
    ψ.ker ≤ Subgroup.center ↥(LargeEvenSLGroup (Fin d) F) := by
  intro u hu
  have h1 : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) u = 1 := by
    have h := hψ u
    rw [show ψ u = 1 from MonoidHom.mem_ker.mp hu] at h
    simpa using h.symm
  have hmem : u ∈ (LargeEvenScalars (Fin d) F).subgroupOf (LargeEvenSLGroup (Fin d) F) := by
    simpa only [LargeEvenProjMk, QuotientGroup.ker_mk'] using (MonoidHom.mem_ker.mpr h1)
  have hc : (u : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) :=
    CFSG.StandardType.TableB.scalars_le_center (Subgroup.mem_subgroupOf.mp hmem)
  rw [Subgroup.mem_center_iff]
  intro v
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hc (v : GL (Fin d) F)

private theorem ker_comp_slEquiv_le_center {Ω : Type} [Group Ω] {m : ℕ}
    {F : Type} [Field F] {ψ : ↥(LargeEvenSLGroup (Fin (m + 1)) F) →* Ω}
    (hker : ψ.ker ≤ Subgroup.center ↥(LargeEvenSLGroup (Fin (m + 1)) F)) :
    (ψ.comp (CFSG.StandardType.InnerDiagA.slEquiv m F).toMonoidHom).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  intro u hu
  have hu' : CFSG.StandardType.InnerDiagA.slEquiv m F u ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp hu
  have hcen := hker hu'
  rw [← Subgroup.map_center_eq (CFSG.StandardType.InnerDiagA.slEquiv m F).symm]
  exact ⟨CFSG.StandardType.InnerDiagA.slEquiv m F u, hcen, by simp⟩

private theorem gacts_to_ggInducedPairs {Ω : Type} [Group Ω] {S : Subgroup Ω} {m : ℕ}
    {F : Type} [Field F] {ψ : ↥(LargeEvenSLGroup (Fin (m + 1)) F) →* ↥S} {b : Ω}
    {A : GL (Fin (m + 1)) F} (h : GActs ψ b A) :
    (b, A⁻¹) ∈ CFSG.StandardType.LinFusion.ggInducedPairs
      ((S.subtype.comp ψ).comp (CFSG.StandardType.InnerDiagA.slEquiv m F).toMonoidHom) := by
  rw [CFSG.StandardType.LinFusion.mem_ggInducedPairs]
  intro u
  have hcoord : (CFSG.StandardType.InnerDiagA.slEquiv m F u : GL (Fin (m + 1)) F) =
      A * (CFSG.StandardType.InnerDiagA.slEquiv m F
        (CFSG.StandardType.InnerDiagA.conjSL A⁻¹ u) : GL (Fin (m + 1)) F) * A⁻¹ := by
    rw [CFSG.StandardType.InnerDiagA.slEquiv_conjSL]
    simp only [MulAut.conjNormal_apply]
    group
  have hg := h (CFSG.StandardType.InnerDiagA.slEquiv m F
      (CFSG.StandardType.InnerDiagA.conjSL A⁻¹ u))
    (CFSG.StandardType.InnerDiagA.slEquiv m F u) hcoord
  have hg' : b * (ψ (CFSG.StandardType.InnerDiagA.slEquiv m F u) : Ω) * b⁻¹ =
      (ψ (CFSG.StandardType.InnerDiagA.slEquiv m F
        (CFSG.StandardType.InnerDiagA.conjSL A⁻¹ u)) : Ω) := by
    rw [hg]
    group
  exact hg'

private theorem exists_ggFrameDiag_of_diagonal {m : ℕ} {F : Type} [Field F]
    {P A : GL (Fin (m + 1)) F} {D : Fin (m + 1) → F}
    (hD : ((P * A * P⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal D) :
    ∃ e : Fin (m + 1) → Fˣ, A = CFSG.StandardType.LinFusion.ggFrameDiag P e := by
  have hU : IsUnit (((P * A * P⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := Units.isUnit (P * A * P⁻¹)
  rw [hD] at hU
  have hDunit : ∀ i, IsUnit (D i) := Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hU)
  let e : Fin (m + 1) → Fˣ := fun i => Units.mk0 (D i) (isUnit_iff_ne_zero.mp (hDunit i))
  refine ⟨e, ?_⟩
  have hdiag : CFSG.StandardType.InnerDiagA.diagGL e = P * A * P⁻¹ := by
    apply Units.ext
    rw [CFSG.StandardType.InnerDiagA.coe_diagGL, hD]
    simp [e]
  calc A = P⁻¹ * (P * A * P⁻¹) * P := by group
    _ = P⁻¹ * CFSG.StandardType.InnerDiagA.diagGL e * P := by rw [← hdiag]
    _ = CFSG.StandardType.LinFusion.ggFrameDiag P e := rfl

private theorem mem_ggFrameBlock_slEquiv_iff {m : ℕ} {F : Type} [Field F]
    {Ω : Type} [Group Ω] (ψ : ↥(LargeEvenSLGroup (Fin (m + 1)) F) →* Ω)
    (P : GL (Fin (m + 1)) F) (I : Finset (Fin (m + 1))) (k : Ω) :
    k ∈ CFSG.StandardType.LinFusion.ggFrameBlock F
        (ψ.comp (CFSG.StandardType.InnerDiagA.slEquiv m F).toMonoidHom) P I ↔
      ∃ u : ↥(LargeEvenSLGroup (Fin (m + 1)) F),
        (P * (u : GL (Fin (m + 1)) F) * P⁻¹) ∈ LinBlockSet (m + 1) F I ∧
          (ψ u : Ω) = k := by
  constructor
  · intro hk
    rw [CFSG.StandardType.LinFusion.ggFrameBlock, Subgroup.mem_map] at hk
    obtain ⟨v, hv, hvk⟩ := hk
    refine ⟨CFSG.StandardType.InnerDiagA.slEquiv m F
      (CFSG.StandardType.InnerDiagA.conjSL P⁻¹ v), ?_, hvk⟩
    have huGL : (CFSG.StandardType.InnerDiagA.slEquiv m F
        (CFSG.StandardType.InnerDiagA.conjSL P⁻¹ v) : GL (Fin (m + 1)) F) =
        P⁻¹ * (CFSG.StandardType.InnerDiagA.slEquiv m F v : GL (Fin (m + 1)) F) * P := by
      rw [CFSG.StandardType.InnerDiagA.slEquiv_conjSL]
      simp only [MulAut.conjNormal_apply]
      group
    have hP : P * (CFSG.StandardType.InnerDiagA.slEquiv m F
        (CFSG.StandardType.InnerDiagA.conjSL P⁻¹ v) : GL (Fin (m + 1)) F) * P⁻¹ =
        (CFSG.StandardType.InnerDiagA.slEquiv m F v : GL (Fin (m + 1)) F) := by
      rw [huGL]
      group
    rw [hP]
    refine ⟨(CFSG.StandardType.InnerDiagA.slEquiv m F v).2, ?_⟩
    intro i j hij
    simpa [CFSG.StandardType.InnerDiagA.coe_slEquiv, Matrix.one_apply] using hv i j hij
  · rintro ⟨u, hu, hψu⟩
    rw [CFSG.StandardType.LinFusion.ggFrameBlock, Subgroup.mem_map]
    let A : ↥(LargeEvenSLGroup (Fin (m + 1)) F) := ⟨P * (u : GL (Fin (m + 1)) F) * P⁻¹, hu.1⟩
    let v : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
      (CFSG.StandardType.InnerDiagA.slEquiv m F).symm A
    refine ⟨v, ?_, ?_⟩
    · intro i j hij
      have hvA : CFSG.StandardType.InnerDiagA.slEquiv m F v = A := by simp [v]
      have hmat : (v : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
          ((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by
        rw [← CFSG.StandardType.InnerDiagA.coe_slEquiv (u := v), hvA]
      rw [hmat]
      have hAu : ((A : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
          if i = j then 1 else 0 := hu.2 i j hij
      rw [hAu, Matrix.one_apply]
    · have hw : CFSG.StandardType.InnerDiagA.slEquiv m F
          (CFSG.StandardType.InnerDiagA.conjSL P⁻¹ v) = u := by
        rw [CFSG.StandardType.InnerDiagA.slEquiv_conjSL]
        have hvA : CFSG.StandardType.InnerDiagA.slEquiv m F v = A := by simp [v]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, hvA]
        change ((P⁻¹ : GL (Fin (m + 1)) F) *
          (P * (u : GL (Fin (m + 1)) F) * P⁻¹) * (P⁻¹)⁻¹ :
            GL (Fin (m + 1)) F) = (u : GL (Fin (m + 1)) F)
        group
      exact (congrArg ψ hw).trans hψu

theorem lin_K_shape {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S) (hψ : GLifts θ ψ) (P : GL (Fin d) F)
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) :
    ∃ I : Finset (Fin d), 2 ≤ I.card ∧
      ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSLGroup (Fin d) F),
        (P * (u : GL (Fin d) F) * P⁻¹) ∈ LinBlockSet d F I ∧ (ψ u : Ω) = k := by
  haveI : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  let ψ' : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Ω :=
    (S.subtype.comp ψ).comp (CFSG.StandardType.InnerDiagA.slEquiv m F).toMonoidHom
  have hψtop : ψ.range = ⊤ := psi_range_top hcfg.qs hψ
  have hrangeS : (S.subtype.comp ψ).range = S := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact (ψ u).2
    · intro hy
      have hs : (⟨y, hy⟩ : ↥S) ∈ ψ.range := by rw [hψtop]; trivial
      obtain ⟨u, hu⟩ := hs
      exact ⟨u, congrArg Subtype.val hu⟩
  have hrangeψ' : ψ'.range = S := by
    have h1 : ψ'.range = (S.subtype.comp ψ).range := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨CFSG.StandardType.InnerDiagA.slEquiv m F u, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨(CFSG.StandardType.InnerDiagA.slEquiv m F).symm u, by simp [ψ']⟩
    rw [h1, hrangeS]
  have hker : ψ.ker ≤ Subgroup.center ↥(LargeEvenSLGroup (Fin (m + 1)) F) :=
    psi_ker_le_center hψ
  have hkerS : (S.subtype.comp ψ).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin (m + 1)) F) := by
    intro u hu
    refine hker (MonoidHom.mem_ker.mpr ?_)
    apply Subtype.ext
    simpa using MonoidHom.mem_ker.mp hu
  have hker' : ψ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    have := ker_comp_slEquiv_le_center (ψ := S.subtype.comp ψ) (m := m) hkerS
    simpa [ψ'] using this
  have hstd : GLAStdSubPre p B x S D K := hcfg.std
  have hcompOpen : CFSG.Open.IsComponentOf K
      (S ⊓ Subgroup.centralizer (D : Set Ω)) := hstd.2.2.2.2.2.1
  have hcomp : CFSG.Assembly.IsComponentOf K
      (ψ'.range ⊓ Subgroup.centralizer (D : Set Ω)) := by
    rw [hrangeψ']
    exact (CFSG.Assembly.isComponentOf_iff_open).mpr hcompOpen
  have hDtor : D ≤ CFSG.StandardType.LinFusion.ggFrameTorus F ψ' P := by
    intro b hb
    obtain ⟨A, hGA, -, Df, hDf⟩ := hB b (hstd.1 hb)
    obtain ⟨e, hAe⟩ := exists_ggFrameDiag_of_diagonal hDf
    have hmem : (b, A⁻¹) ∈ CFSG.StandardType.LinFusion.ggInducedPairs ψ' := by
      simpa [ψ'] using gacts_to_ggInducedPairs (S := S) (ψ := ψ) hGA
    have hAinv : A⁻¹ = CFSG.StandardType.LinFusion.ggFrameDiag P e⁻¹ := by
      rw [hAe, CFSG.StandardType.LinFusion.ggFrameDiag_inv]
    rw [hAinv] at hmem
    exact ⟨e⁻¹, hmem⟩
  obtain ⟨I, hK, -⟩ :=
    CFSG.StandardType.LinSemisimple.exists_eq_ggFrameBlock_of_le_ggFrameTorus
      (m := m) (F := F) (G := Ω) (ψ := ψ') hker' P hDtor hcomp
  have hI2 : 2 ≤ I.card := by
    have hqK : CFSG.Assembly.IsQuasisimple K := hcomp.2.2
    have hle : K ≤ (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F) I).map
        (ψ'.comp (CFSG.StandardType.InnerDiagA.conjSL P⁻¹)) := by
      rw [hK, CFSG.StandardType.LinFusion.ggFrameBlock]
    exact (CFSG.StandardType.LinSemisimple.two_le_card_of_isQuasisimple_le
      (m := m) (F := F) (G := Ω) (ψ := ψ'.comp (CFSG.StandardType.InnerDiagA.conjSL P⁻¹))
      (I := I) hqK hle).1
  refine ⟨I, hI2, ?_⟩
  intro k
  rw [hK]
  exact mem_ggFrameBlock_slEquiv_iff (S.subtype.comp ψ) P I k

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
