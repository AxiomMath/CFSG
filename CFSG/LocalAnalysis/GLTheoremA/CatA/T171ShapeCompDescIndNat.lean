module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (glaPComponent_map_central)

theorem componentDescentIndAut_inv_holds :
    ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
      {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (y : R)
      (hS : Setup p L J A d b),
      LargeEvenInduces θ (conjRel b) (MulAut.conj y) →
      ∀ hN : y ∈ Subgroup.normalizer
          (((J.subgroupOf L).map (piCenterQuot θ)) : Set R),
        ∃ e : PSimple p J ≃* PSimple p ((J.subgroupOf L).map (piCenterQuot θ)),
          MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm) =
            CFSG.LocalAnalysis.GLTheoremA.MI.indAut p
              ((J.subgroupOf L).map (piCenterQuot θ)) y⁻¹ (Subgroup.inv_mem _ hN) := by
  intro G _ _ p L J A d b R _ _ θ y hS hind hN
  classical
  have hp : p.Prime := hS.prime
  have hJL : J ≤ L := hS.comp.1.1.trans inf_le_left
  let π : ↥L →* R := piCenterQuot θ
  have hπker : π.ker ≤ Subgroup.center ↥L := by
    rw [show π.ker = Subgroup.center ↥L from by
      dsimp only [π, piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.b_mem
  have hXle : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ L := inf_le_left
  have hJ' : GLAPComponent p ((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L)
      (J.subgroupOf L) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp hXle hS.pcomp
  have hc : ∀ z ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L ⊓ π.ker,
      ∀ x ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L, x * z = z * x := by
    intro z hz x _hx
    have hzc : z ∈ Subgroup.center ↥L := hπker hz.2
    exact Subgroup.mem_center_iff.1 hzc x
  have hJbar : GLAPComponent p
      (((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π)
      ((J.subgroupOf L).map π) :=
    glaPComponent_map_central hp π hc hJ'
  let Jbar : Subgroup R := (J.subgroupOf L).map π
  have hJbar' : GLAPComponent p
      (((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π) Jbar := hJbar
  have hN' : y⁻¹ ∈ Subgroup.normalizer (Jbar : Set R) := Subgroup.inv_mem _ hN
  let πJ : ↥J →* R := π.comp (Subgroup.inclusion hJL)
  let fJ : ↥J →* ↥Jbar :=
    πJ.codRestrict Jbar fun j =>
      Subgroup.mem_map.mpr ⟨⟨(j : G), hJL j.2⟩, j.2, rfl⟩
  have hfJ : Function.Surjective fJ := by
    intro z
    obtain ⟨l, hl, hz⟩ := Subgroup.mem_map.mp z.2
    have hlj : (l : G) ∈ J := Subgroup.mem_subgroupOf.mp hl
    refine ⟨⟨(l : G), hlj⟩, ?_⟩
    apply Subtype.ext
    exact hz
  let ψ : PSimple p J →* PSimple p Jbar :=
    CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective hp fJ hfJ
  have hψsurj : Function.Surjective ψ :=
    CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective_surjective hp fJ hfJ
  have hψmk : ∀ l : ↥J, ψ (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk (fJ l)) :=
    fun l => by
      simp [ψ, CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective,
        CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_mk]
  have hsimpleJ : IsSimpleGroup (PSimple p J) :=
    (CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hS.pcomp).1
  have hnaBar : ∃ a b' : PSimple p Jbar, a * b' ≠ b' * a :=
    (CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hJbar').2
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b', hab⟩ := hnaBar
      obtain ⟨a', rfl⟩ := hψsurj a
      obtain ⟨b'', rfl⟩ := hψsurj b'
      apply hab
      have h1 : ψ a' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      have h2 : ψ b'' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      rw [h1, h2]
  let e0 : PSimple p J ≃* PSimple p Jbar :=
    MulEquiv.ofBijective ψ ⟨hinj, hψsurj⟩
  have he0 : ∀ x, e0 x = ψ x := fun _ => rfl
  have hkey : ∀ l : ↥J,
      e0 (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
          (QuotientGroup.mk (QuotientGroup.mk l))) =
        CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹ hN'
          (e0 (QuotientGroup.mk (QuotientGroup.mk l))) := by
    intro l
    have hmem : b⁻¹ * (l : G) * b ∈ J := by
      have hbinv : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hS.b_norm
      have := (Subgroup.mem_normalizer_iff.mp hbinv (l : G)).mp l.2
      simpa using this
    let l' : ↥J := ⟨b⁻¹ * (l : G) * b, hmem⟩
    have hrel : indRel p J b (QuotientGroup.mk l) (QuotientGroup.mk l') :=
      ⟨l, l', rfl, rfl, rfl⟩
    have hstep : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
        (QuotientGroup.mk (QuotientGroup.mk l)) = QuotientGroup.mk (QuotientGroup.mk l') :=
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut_apply_mk hS.b_norm hrel
    have hmemL : b⁻¹ * (l : G) * b ∈ L := hJL hmem
    let lL : ↥L := Subgroup.inclusion hJL l
    let lL' : ↥L := Subgroup.inclusion hJL l'
    have hrelL : (lL' : G) = b⁻¹ * (lL : G) * b := by
      simp [lL, lL', l']
    have hInd := hind lL lL' hrelL
    have hπl' : (fJ l' : R) = y * (fJ l : R) * y⁻¹ := by
      simpa [fJ, πJ, π, piCenterQuot, lL, lL', MulAut.conj_apply] using hInd.symm
    have hrelBar : indRel p Jbar y⁻¹ (QuotientGroup.mk (fJ l))
        (QuotientGroup.mk (fJ l')) := by
      refine ⟨fJ l, fJ l', rfl, rfl, ?_⟩
      show ((fJ l' : ↥Jbar) : R) = (y⁻¹)⁻¹ * ((fJ l : ↥Jbar) : R) * y⁻¹
      simpa using hπl'
    have hstepBar : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹ hN'
        (QuotientGroup.mk (QuotientGroup.mk (fJ l))) =
          QuotientGroup.mk (QuotientGroup.mk (fJ l')) :=
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut_apply_mk hN' hrelBar
    calc e0 (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
          (QuotientGroup.mk (QuotientGroup.mk l)))
        = e0 (QuotientGroup.mk (QuotientGroup.mk l')) := by rw [hstep]
      _ = QuotientGroup.mk (QuotientGroup.mk (fJ l')) := by rw [he0, hψmk]
      _ = CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹ hN'
            (QuotientGroup.mk (QuotientGroup.mk (fJ l))) := hstepBar.symm
      _ = CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Jbar y⁻¹ hN'
            (e0 (QuotientGroup.mk (QuotientGroup.mk l))) := by rw [he0, hψmk l]
  refine ⟨e0, ?_⟩
  ext x
  obtain ⟨y, hy⟩ := e0.surjective x
  rw [← hy]
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hkey l

theorem componentDescentIndAut_holds : ComponentDescentIndAut :=
  componentDescentIndAut_inv_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
