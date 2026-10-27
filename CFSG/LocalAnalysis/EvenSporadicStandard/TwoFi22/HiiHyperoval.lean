module

public import CFSG.Fischer.Uniq.F24Hyperoval

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem mul_mul_mem_of_conj (hinv : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hD2 : ∀ x ∈ E, x * x = 1) {x y : X} (hx : x ∈ E) (hy : y ∈ E) : x * y * x ∈ E := by
  have h := hinv x y hy
  rwa [inv_eq_of_mul_eq_one_right (hD2 x hx)] at h

theorem mul_mul_mem_muSet_of_conj (hinv : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hD2 : ∀ x ∈ E, x * x = 1) {d c s s' : X} (hs : s ∈ muSet E d c)
    (hs' : s' ∈ muSet E d c) : s * s' * s ∈ muSet E d c :=
  ⟨mul_mul_mem_localClass_of_inv hD2 ⟨s, hs.1⟩ ⟨s', hs'.1⟩
      (mul_mul_mem_of_conj hinv hD2 hs.1.1 hs'.1.1),
    mul_mul_mem_localClass_of_inv hD2 ⟨s, hs.2⟩ ⟨s', hs'.2⟩
      (mul_mul_mem_of_conj hinv hD2 hs.2.1 hs'.2.1)⟩

namespace LocalPoints

variable (hF : Pair Y F) {e : X} (L : LocalPoints (pairModel hF) E e)

theorem restrictStar_tau_of_conj (hinv : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hD2 : ∀ x ∈ E, x * x = 1) (f : LocalClass E e)
    (g h : ↥(LocalClass E e ∩ LocalClass E f)) :
    ∃ hm : (g : X) * h * g ∈ LocalClass E e ∩ LocalClass E f,
      ((L.restrictStar hF f ⟨_, hm⟩ : Y)) =
        L.restrictStar hF f g * L.restrictStar hF f h * L.restrictStar hF f g := by
  have hE : (g : X) * h * g ∈ E := mul_mul_mem_of_conj hinv hD2 g.2.1.1 h.2.1.1
  have hm1 := mul_mul_mem_localClass_of_inv hD2 ⟨g, g.2.1⟩ ⟨h, h.2.1⟩ hE
  have hm2 := mul_mul_mem_localClass_of_inv hD2 ⟨g, g.2.2⟩ ⟨h, h.2.2⟩ hE
  refine ⟨⟨hm1, hm2⟩, ?_⟩
  rw [restrictStar_val]
  exact congrArg Subtype.val (L.tau ⟨g, g.2.1⟩ ⟨h, h.2.1⟩ hm1)

end LocalPoints

section LocallyHyperoval

variable (hPF : PolarFacts) (hF1 : LinesByPerp) (hF : F22 Y F)
  (hconnF : (commGraph F).Connected)
  (hinv : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) (hD2 : ∀ x ∈ E, x * x = 1)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel hF.1) E f))
include hPF hF1 hF hconnF hinv hD2 hloc

theorem muImg_inter_localClass_of_conj
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
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
      (tau_symm_of_tau _ (Lf.restrictStar_tau_of_conj hF.1 hinv hD2 ⟨d, hdf⟩))
    rw [hA, Set.inter_comm (LocalClass E f)] at h1
    exact h1.transport ψB (L.restrictStar_comm hF.1 f) (L.restrictStar_tau_of_conj hF.1 hinv hD2 f)

theorem isLocallyHyperoval_muImg_of_conj
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel hF.1) E d) :
    IsLocallyHyperoval F (Subtype.val '' L.muImg c) := by
  refine ⟨?_, ?_, fun s hs => (muImg_inter_localClass_of_conj hPF hF1 hF hconnF hinv hD2 hloc hd
    hc L hs).1, fun s hs => (muImg_inter_localClass_of_conj hPF hF1 hF hconnF hinv hD2 hloc hd
    hc L hs).2⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hm : (f : X) * g * f ∈ muSet E d c :=
      mul_mul_mem_muSet_of_conj hinv hD2 ⟨f.2, hf⟩ ⟨g.2, hg⟩
    exact ⟨_, ⟨⟨_, hm.1⟩, hm.2, rfl⟩, congrArg Subtype.val (L.tau f g hm.1)⟩

end LocallyHyperoval

end CFSG.Fischer
