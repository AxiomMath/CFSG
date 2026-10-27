module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinCentQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinBlkComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinBlkCent
public import CFSG.CGT.Foote82.T66.BranchAGen
public import CFSG.CGT.Foote82.T66.BranchARecog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups commutatorElement

theorem lin_component_of_diag {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) {a : ↥(LinSL d F)}
    (hdiag : ∀ i j : Fin d, i ≠ j → ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0)
    (hap : (a : GL (Fin d) F) ^ p = 1) (ha1 : LinMk d F a ≠ 1) {K₁ : Subgroup (LinPSL d F)}
    (hK : CFSG.Open.IsComponentOf K₁
      (Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F)))) :
    ∃ I : Finset (Fin d), LinLevelSet (a : GL (Fin d) F) I ∧ 2 ≤ I.card ∧
      K₁ = LinBlockSub d F I := by
  by_contra hcon
  push Not at hcon
  have hC : ∀ g : ↥(LinSL d F),
      LinMk d F g ∈ Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F)) →
        (g : GL (Fin d) F) * a = a * g := fun g hg => lin_centralizer_quot h hap hg
  have hcomm : ∀ I : Finset (Fin d), LinLevelSet (a : GL (Fin d) F) I → 2 ≤ I.card →
      ∀ k ∈ K₁, ∀ e ∈ LinBlockSub d F I, e * k = k * e := by
    intro I hI hcard k hk e he
    have hE := lin_block_component h hdiag ha1 hC hI hcard
    rcases CFSG.CGT.Foote82.BranchAAux.eq_or_commute_of_isComponentOf hK hE with h1 | h1
    · exact absurd h1 (hcon I hI hcard)
    · have h2 : ⁅k, e⁆ ∈ (⁅K₁, LinBlockSub d F I⁆ : Subgroup (LinPSL d F)) :=
        Subgroup.commutator_mem_commutator hk he
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
  have hdK : ∀ k ∈ K₁, k ∈ LinDiagImage d F := by
    intro k hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ k
    exact lin_cent_blocks_diag hdiag (hC g (hK.1 hk))
      (fun I hI hcard e he => hcomm I hI hcard _ hk e he)
  obtain ⟨-, hsimple⟩ := hK.2.2
  haveI := hsimple
  obtain ⟨q1, q2, hq⟩ := exists_pair_ne (↥K₁ ⧸ Subgroup.center ↥K₁)
  obtain ⟨w1, rfl⟩ := QuotientGroup.mk_surjective q1
  obtain ⟨w2, rfl⟩ := QuotientGroup.mk_surjective q2
  apply hq
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  exact lin_diagImage_comm (hdK _ w.2) (hdK _ (w1⁻¹ * w2).2)

theorem lin_component_support {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) {Q : Type} [Group Q] {ψ : Q ≃* LinPSL d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : LinDiagFrame p d F ψ Bbar A) {y : Q} (hy : y ∈ Bbar)
    (hy1 : y ≠ 1) {Kbar : Subgroup Q}
    (hK : CFSG.Open.IsComponentOf Kbar (Subgroup.centralizer ({y} : Set Q))) :
    ∃ I : Finset (Fin d), 2 ≤ I.card ∧
      (Kbar.map ψ.toMonoidHom : Set (LinPSL d F)) = LinBlockImage d F I := by
  obtain ⟨-, hAe, hAd, hAB⟩ := hfr
  have hy' : ψ y ∈ Bbar.map ψ.toMonoidHom := ⟨y, hy, rfl⟩
  rw [hAB] at hy'
  obtain ⟨a, ha, hay⟩ := hy'
  have haA : (a : GL (Fin d) F) ∈ A := ha
  have hap : (a : GL (Fin d) F) ^ p = 1 := hAe.2 _ haA
  have ha1 : LinMk d F a ≠ 1 := by
    intro h1
    apply hy1
    apply ψ.injective
    rw [map_one]
    exact hay.symm.trans h1
  have hK1 : CFSG.Open.IsComponentOf (Kbar.map ψ.toMonoidHom)
      (Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F))) := by
    have h1 := CFSG.CGT.Foote82.BranchAAux.isComponentOf_map_equiv ψ hK
    have h2 : (Subgroup.centralizer ({y} : Set Q)).map ψ.toMonoidHom =
        Subgroup.centralizer ({LinMk d F a} : Set (LinPSL d F)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hw
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        show ψ w * LinMk d F a = LinMk d F a * ψ w
        rw [hay, ← map_mul, ← map_mul, hw']
      · intro hz
        have hz' : z * LinMk d F a = LinMk d F a * z :=
          Subgroup.mem_centralizer_singleton_iff.mp hz
        rw [hay] at hz'
        refine ⟨ψ.symm z, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hz'
    rwa [h2] at h1
  obtain ⟨I, -, hI2, hKI⟩ := lin_component_of_diag h (hAd _ haA) hap ha1 hK1
  refine ⟨I, hI2, ?_⟩
  rw [← coe_linBlockSub, ← hKI]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
