module

public import CFSG.Fischer.Uniq.PolarIntrinsic
public import CFSG.Fischer.Uniq.LHTransport
public import CFSG.Fischer.Uniq.F22

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y Z : Type} [Group X] [Group Y] [Group Z] {E : Set X} {F : Set Y} {D : Set Z}

theorem Pair.isHyperovalIn_muSet (hPF : PolarFacts) (hF1 : LinesByPerp) (hP : Pair Z D)
    (hloc : ∀ f ∈ D, Nonempty (LocalPoints polarModel D f)) {p q : Z} (hp : p ∈ D)
    (hq : q ∈ D) (hpq : q * p ≠ p * q) : IsHyperovalIn (LocalClass D p) (muSet D p q) := by
  obtain ⟨L⟩ := hloc p hp
  have hsub : muSet D p q ⊆ LocalClass D p := fun _ h => h.1
  rw [L.isHyperovalIn_iff hF1 hP hsub]
  have : L.pts (muSet D p q) = L.muImg q := by
    ext r
    rw [LocalPoints.mem_pts, L.mem_muImg]
    exact ⟨fun h => h.2, fun h => ⟨(L.χ.symm r).2, h⟩⟩
  rw [this]
  exact Pair.isClosedHyperoval_muImg hPF hP hp hq hpq L hloc

namespace LocalPoints

variable (hF : Pair Y F) {e : X} (L : LocalPoints (pairModel hF) E e)

theorem mem_localClass_iff (f g : LocalClass E e) :
    (g : X) ∈ LocalClass E f ↔ ((L.χ g : F) : Y) ∈ LocalClass F (L.χ f : Y) := by
  constructor
  · rintro ⟨-, hne, hc⟩
    refine ⟨(L.χ g).2, fun h => hne ?_, ((L.comm g f).1 hc)⟩
    exact congrArg Subtype.val (L.χ.injective (Subtype.ext h))
  · rintro ⟨-, hne, hc⟩
    refine ⟨g.2.1, fun h => hne ?_, (L.comm g f).2 hc⟩
    rw [show g = f from Subtype.ext h]

@[expose] noncomputable def restrictStar (f : LocalClass E e) :
    ↥(LocalClass E e ∩ LocalClass E f) ≃ ↥(LocalClass F (L.χ f : Y)) where
  toFun g := ⟨L.χ ⟨g, g.2.1⟩, (L.mem_localClass_iff hF f ⟨g, g.2.1⟩).1 g.2.2⟩
  invFun y := ⟨L.χ.symm ⟨y, y.2.1⟩, (L.χ.symm ⟨y, y.2.1⟩).2, by
    rw [L.mem_localClass_iff hF f, Equiv.apply_symm_apply]
    exact y.2⟩
  left_inv g := by simp
  right_inv y := by simp

theorem restrictStar_val (f : LocalClass E e) (g : ↥(LocalClass E e ∩ LocalClass E f)) :
    ((L.restrictStar hF f g : Y)) = (L.χ ⟨g, g.2.1⟩ : Y) := rfl

theorem restrictStar_comm (f : LocalClass E e) (g h : ↥(LocalClass E e ∩ LocalClass E f)) :
    (g : X) * h = h * g ↔
      ((L.restrictStar hF f g : Y)) * L.restrictStar hF f h =
        L.restrictStar hF f h * L.restrictStar hF f g :=
  L.comm ⟨g, g.2.1⟩ ⟨h, h.2.1⟩

theorem restrictStar_tau (hE : Pair X E) (f : LocalClass E e)
    (g h : ↥(LocalClass E e ∩ LocalClass E f)) :
    ∃ hm : (g : X) * h * g ∈ LocalClass E e ∩ LocalClass E f,
      ((L.restrictStar hF f ⟨_, hm⟩ : Y)) =
        L.restrictStar hF f g * L.restrictStar hF f h * L.restrictStar hF f g := by
  have hm1 := LocalPoints.mul_mul_mem_localClass hE ⟨g, g.2.1⟩ ⟨h, h.2.1⟩
  have hm2 := LocalPoints.mul_mul_mem_localClass hE ⟨g, g.2.2⟩ ⟨h, h.2.2⟩
  refine ⟨⟨hm1, hm2⟩, ?_⟩
  rw [restrictStar_val]
  exact congrArg Subtype.val (L.tau ⟨g, g.2.1⟩ ⟨h, h.2.1⟩ hm1)

end LocalPoints

section LocallyHyperoval

variable (hPF : PolarFacts) (hF1 : LinesByPerp) (hF : F22 Y F)
  (hconnF : (commGraph F).Connected) (hE : Pair X E)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel hF.1) E f))
include hPF hF1 hF hconnF hE hloc

theorem Pair.muImg_inter_localClass {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel hF.1) E d) {s : Y} (hs : s ∈ Subtype.val '' L.muImg c) :
    (Subtype.val '' L.muImg c ∩ LocalClass F s).Nonempty ∧
      IsHyperovalIn (LocalClass F s) (Subtype.val '' L.muImg c ∩ LocalClass F s) := by
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints polarModel F f) :=
    fun f hf => F22.nonempty_localPoints hF hf
  obtain ⟨_, ⟨f, hfc, rfl⟩, rfl⟩ := hs
  have hdf : d ∈ LocalClass E f := ⟨hd, f.2.2.1.symm, f.2.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc.1, hfc.2.1.symm, hfc.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f f.2.1
  set pf := Lf.χ ⟨d, hdf⟩
  set qf := Lf.χ ⟨c, hcf⟩
  have hpq : (qf : Y) * pf ≠ pf * qf := fun h => hc.2.1 ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).2 h)
  set N : Set X := muSet E d c ∩ LocalClass E f
  set ψA := (Lf.restrictStar hF.1 ⟨d, hdf⟩).symm
  have hA : imgIn ψA (muSet F pf qf) = N := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      set g := ψA y
      have hy' : (Lf.restrictStar hF.1 ⟨d, hdf⟩ g : Y) = y := by
        rw [Equiv.apply_symm_apply]
      rw [← hy', LocalPoints.restrictStar_val] at hy
      exact ⟨⟨(Lf.mem_localClass_iff hF.1 ⟨d, hdf⟩ ⟨g, g.2.1⟩).2 hy.1,
        (Lf.mem_localClass_iff hF.1 ⟨c, hcf⟩ ⟨g, g.2.1⟩).2 hy.2⟩, g.2.1⟩
    · rintro ⟨⟨hzd, hzc⟩, hzf⟩
      refine ⟨Lf.restrictStar hF.1 ⟨d, hdf⟩ ⟨z, hzf, hzd⟩, ?_, by simp [ψA]⟩
      rw [LocalPoints.restrictStar_val]
      exact ⟨(Lf.mem_localClass_iff hF.1 ⟨d, hdf⟩ ⟨z, hzf⟩).1 hzd,
        (Lf.mem_localClass_iff hF.1 ⟨c, hcf⟩ ⟨z, hzf⟩).1 hzc⟩
  set ψB := L.restrictStar hF.1 f
  have hB : imgIn ψB N = Subtype.val '' L.muImg c ∩ LocalClass F (L.χ f : Y) := by
    ext y
    constructor
    · rintro ⟨g, ⟨⟨-, hgc⟩, -⟩, rfl⟩
      exact ⟨⟨_, ⟨⟨g, g.2.1⟩, hgc, rfl⟩, rfl⟩, (ψB g).2⟩
    · rintro ⟨⟨_, ⟨g, hgc, rfl⟩, rfl⟩, hgf⟩
      have hgf' : (g : X) ∈ LocalClass E f := (L.mem_localClass_iff hF.1 f g).2 hgf
      exact ⟨⟨g, g.2, hgf'⟩, ⟨⟨g.2, hgc⟩, hgf'⟩, rfl⟩
  rw [← hB]
  constructor
  · rw [← hA]
    obtain ⟨y, hy⟩ := Pair.muSet_nonempty hF.1 hconnF pf.2 qf.2 hpq
    set y' : LocalClass F (pf : Y) := ⟨y, hy.1⟩
    have h1 : ((ψA y' : _) : X) ∈ imgIn ψA (muSet F pf qf) := ⟨y', hy, rfl⟩
    exact ⟨_, ⟨⟨(ψA y' : X), (ψA y').2.2, (ψA y').2.1⟩, h1, rfl⟩⟩
  · have h1 := (Pair.isHyperovalIn_muSet hPF hF1 hF.1 hlocF pf.2 qf.2 hpq).transport ψA
      (comm_symm_of_comm _ (Lf.restrictStar_comm hF.1 ⟨d, hdf⟩))
      (tau_symm_of_tau _ (Lf.restrictStar_tau hF.1 hE ⟨d, hdf⟩))
    rw [hA, Set.inter_comm (LocalClass E f)] at h1
    exact h1.transport ψB (L.restrictStar_comm hF.1 f) (L.restrictStar_tau hF.1 hE f)

theorem Pair.isLocallyHyperoval_muImg {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel hF.1) E d) :
    IsLocallyHyperoval F (Subtype.val '' L.muImg c) := by
  refine ⟨?_, ?_, fun s hs => (Pair.muImg_inter_localClass hPF hF1 hF hconnF hE hloc hd hc L
    hs).1, fun s hs => (Pair.muImg_inter_localClass hPF hF1 hF hconnF hE hloc hd hc L hs).2⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hm : (f : X) * g * f ∈ muSet E d c := Pair.mul_mul_mem_muSet hE ⟨f.2, hf⟩ ⟨g.2, hg⟩
    exact ⟨_, ⟨⟨_, hm.1⟩, hm.2, rfl⟩, congrArg Subtype.val (L.tau f g hm.1)⟩

end LocallyHyperoval

end CFSG.Fischer
