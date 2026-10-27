module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section I1429Inner


open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem i1429_inner_carrier (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 3)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (s : (TauCeti.CFSGIndex.lie d).Group) (hs : orderOf s = 3)
    (I : Subgroup (TauCeti.CFSGIndex.lie d).Group) :
    ¬ GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)) I := by
  intro hI
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s) =
      Subgroup.centralizer ({s} : Set (TauCeti.CFSGIndex.lie d).Group) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff,
      MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hLay : GLAPLayer 3 (Subgroup.centralizer ({s} : Set (TauCeti.CFSGIndex.lie d).Group)) = ⊥ :=
    kdCharP_holds Nat.prime_three (by norm_num) d hd s hs
  have hle : I ≤ GLAPLayer 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)) := by
    unfold GLAPLayer
    exact le_sSup hI
  rw [hfix, hLay] at hle
  exact glaPComponent_ne_bot' hI (le_bot_iff.1 hle)

theorem i1429_inner_lie_simple {Q : Type} [Group Q] [Finite Q] (hZ : Subgroup.center Q = ⊥)
    (hcat : catalogIs Q (onLie fun d => d.characteristic = 3)) (q : Q)
    (h3 : (MulAut.conj q) ^ 3 = 1) (h1 : MulAut.conj q ≠ 1) (I : Subgroup Q) :
    ¬ GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj q)) I := by
  intro hI
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have key : ∃ d : TauCeti.ValidLieTypeIndex, i = TauCeti.CFSGIndex.lie d ∧ d.1.characteristic = 3 := by
    cases i <;> first | exact ⟨_, rfl, hi⟩ | exact (hi : False).elim
  obtain ⟨d, rfl, hd⟩ := key
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv Q e.toEquiv
  have hq1 : q ≠ 1 := fun h => h1 (by rw [h, map_one])
  have hq3 : q ^ 3 = 1 := by
    have h' : MulAut.conj (q ^ 3) = 1 := by rw [map_pow, h3]
    have hmem : q ^ 3 ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut Q => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [hZ] at hmem
    exact (Subgroup.mem_bot).1 hmem
  have hq : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hs : orderOf (e q) = 3 := by rw [MulEquiv.orderOf_eq, hq]
  have hcongr : MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) := by
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  have hT := chevQ_transport Nat.prime_three e hI
  rw [hcongr] at hT
  exact i1429_inner_carrier d hd (e q) hs _ hT.1

end I1429Inner

end CFSG.LocalAnalysis.GLTheoremA

end
