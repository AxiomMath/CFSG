module

public import Certificates.Data.Kernel.OpsReal
public import CFSG.Certificates.Kernel.OpsV4Sound

public section

namespace CFSG.KC.OpsReal

open CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB CFSG.RankThree.PartTwo.Census
  CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.OpsHom CFSG.KC.OpsV4

theorem any_of_sim {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V} (S : Sim O₀ O)
    {X : M} {x : Nat} (hX : S.R X x) {tests : List Nat} (hT : ∀ k ∈ tests, S.T k)
    (h : tests.any (fun k => O.vne (O.vmul (O.unit k) x) (O.unit k)) = true) :
    tests.any (fun k => O₀.vne (O₀.vmul (O₀.unit k) X) (O₀.unit k)) = true := by
  obtain ⟨k, hk, hv⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨k, hk, S.vne (S.vmul (S.unit (hT k hk)) hX) (S.unit (hT k hk)) hv⟩

theorem checkElem_of_sim {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V}
    (S : Sim O₀ O) {D : RealData} (hp : D.base.prog.all (Op.lt D.base.nregs) = true)
    (hr : [D.t₁, D.t₂, D.x, D.d].all (decide <| · < D.base.nregs) = true) {g : Nat → Nat}
    (hg : ∀ r, r < D.base.nregs → S.R (O₀.run D.base.prog (O₀.initRegs (O₀.decode D.base.seedA)
      (O₀.decode D.base.seedB) D.base.nregs))[r]! (g r))
    (hT : ∀ k ∈ D.base.tests, S.T k) (hE : S.E D.dord) (h : realG O S.pw D g = true) :
    RealData.checkElem O₀ D = true := by
  have hr' := hr
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hr'
  obtain ⟨h1, h2, hx, hd⟩ := hr'
  have r1 := hg _ h1
  have r2 := hg _ h2
  have rx := hg _ hx
  have rd := hg _ hd
  unfold realG at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩ := h
  unfold RealData.checkElem
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hp, hr⟩, ?_⟩
  unfold RealData.localOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨S.eq (S.mul r1 r1) S.one e1, S.eq (S.mul r2 r2) S.one e2⟩, S.commOK r1 r2 e3⟩,
    any_of_sim S r1 hT e4⟩, S.conjOK rx r1 r1 r2 e5⟩, S.conjOK rx r2 r1 r2 e6⟩,
    S.eq (S.mul (S.mul rx rx) rx) S.one e7⟩, any_of_sim S rx hT e8⟩, e9⟩,
    S.eq (S.pow rd hE) S.one e10⟩, S.eq (S.mul rd rx) (S.mul (S.mul rx rx) rd) e11⟩

theorem checkElem_of_N {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V}
    (H : Hom O₀ O) {A B : Nat} {D : RealData} (eA : O₀.decode D.base.seedA = H.U A)
    (eB : O₀.decode D.base.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : realN O A B D = true) : RealData.checkElem O₀ D = true := by
  unfold realN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hr⟩, hrun⟩ := h
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N H eA eB hA hB hp hrun
  exact checkElem_of_sim (Sim.ofHom H) hp hr (g := getN Rl)
    (fun r hr => hR.2 r (by rw [hlen]; exact hr)) (fun _ _ => trivial) trivial hk

end CFSG.KC.OpsReal

end
