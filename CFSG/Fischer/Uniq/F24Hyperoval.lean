module

public import CFSG.Fischer.Uniq.F23Hyperoval

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y]

structure IsLocally351 (D T : Set X) : Prop where
  subset : T ⊆ D
  closed : ∀ s ∈ T, ∀ t ∈ T, s * t * s ∈ T
  nonempty : ∀ s ∈ T, (T ∩ LocalClass D s).Nonempty
  locally : ∀ s ∈ T, IsLocallyHyperoval (LocalClass D s) (T ∩ LocalClass D s)

section Transport

variable {A : Set X} {A' : Set Y} (φ : A ≃ A')
  (hcomm : ∀ x y : A, (x : X) * y = y * x ↔ (φ x : Y) * φ y = φ y * φ x)
  (htau : ∀ x y : A, ∃ h : (x : X) * y * x ∈ A, (φ ⟨_, h⟩ : Y) = φ x * φ y * φ x)
include hcomm

theorem mem_localClass_iff_of_equiv (s y : A) :
    (y : X) ∈ LocalClass A s ↔ (φ y : Y) ∈ LocalClass A' (φ s) := by
  constructor
  · rintro ⟨-, hne, hc⟩
    refine ⟨(φ y).2, fun h => hne ?_, (hcomm y s).1 hc⟩
    exact congrArg Subtype.val (φ.injective (Subtype.ext h))
  · rintro ⟨-, hne, hc⟩
    refine ⟨y.2, fun h => hne ?_, (hcomm y s).2 hc⟩
    rw [show y = s from Subtype.ext h]

@[expose] noncomputable def restrictLocal (s : A) :
    ↥(LocalClass A s) ≃ ↥(LocalClass A' (φ s : Y)) where
  toFun y := ⟨φ ⟨y, y.2.1⟩, (mem_localClass_iff_of_equiv φ hcomm s ⟨y, y.2.1⟩).1 y.2⟩
  invFun y := ⟨φ.symm ⟨y, y.2.1⟩, by
    rw [mem_localClass_iff_of_equiv φ hcomm s, Equiv.apply_symm_apply]
    exact y.2⟩
  left_inv y := by simp
  right_inv y := by simp

theorem restrictLocal_val (s : A) (y : ↥(LocalClass A s)) :
    ((restrictLocal φ hcomm s y : Y)) = (φ ⟨y, y.2.1⟩ : Y) := rfl

theorem imgIn_inter_localClass (U : Set X) (s : A) :
    imgIn (restrictLocal φ hcomm s) (U ∩ LocalClass A s) =
      imgIn φ U ∩ LocalClass A' (φ s : Y) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzU, -⟩, rfl⟩
    exact ⟨⟨⟨z, z.2.1⟩, hzU, rfl⟩, (restrictLocal φ hcomm s z).2⟩
  · rintro ⟨⟨z, hzU, rfl⟩, hz⟩
    have hz' : (z : X) ∈ LocalClass A s := (mem_localClass_iff_of_equiv φ hcomm s z).2 hz
    exact ⟨⟨z, hz'⟩, ⟨hzU, hz'⟩, rfl⟩

include htau

omit hcomm htau in
theorem mul_mul_mem_localClass_of_inv (hinv : ∀ x ∈ A, x * x = 1) {s : X}
    (x y : LocalClass A s) (h : (x : X) * y * x ∈ A) : (x : X) * y * x ∈ LocalClass A s := by
  have hx : (x : X) * x = 1 := hinv x x.2.1
  have h1 : Commute (x : X) s := x.2.2.2
  have h2 : Commute (y : X) s := y.2.2.2
  refine ⟨h, fun e => y.2.2.1 ?_, ((h1.mul_left h2).mul_left h1 : Commute ((x : X) * y * x) s)⟩
  calc (y : X) = x * (x * y * x) * x := by
        rw [show (x : X) * (x * y * x) * x = (x * x) * y * (x * x) by group, hx, one_mul, mul_one]
    _ = x * s * x := by rw [e]
    _ = s := by rw [h1.eq, mul_assoc, hx, mul_one]

theorem IsLocallyHyperoval.transport (hinv : ∀ x ∈ A, x * x = 1) {U : Set X}
    (hU : IsLocallyHyperoval A U) :
    IsLocallyHyperoval A' (imgIn φ U) := by
  refine ⟨imgIn_subset φ U, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨h, e⟩ := htau x y
    rw [← e]
    exact ⟨⟨_, h⟩, hU.closed x hx y hy, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← imgIn_inter_localClass φ hcomm]
    obtain ⟨z, hz⟩ := hU.nonempty s hs
    exact ⟨_, ⟨⟨z, hz.2⟩, hz, rfl⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← imgIn_inter_localClass φ hcomm]
    refine (hU.hyperoval s hs).transport (restrictLocal φ hcomm s) (fun x y => ?_)
      (fun x y => ?_)
    · exact hcomm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
    · obtain ⟨h, e⟩ := htau ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
      refine ⟨mul_mul_mem_localClass_of_inv hinv x y h, ?_⟩
      rw [restrictLocal_val]
      exact e

end Transport

section Locally351

variable {E : Set X} {F : Set Y} (hF : Pair Y F) (hE : Pair X E)
  (hMF : ∀ p q, p ∈ F → q ∈ F → q * p ≠ p * q → (muSet F p q).Nonempty ∧
    IsLocallyHyperoval (LocalClass F p) (muSet F p q))
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel hF) E f))
include hF hE hMF hloc

theorem Pair.muImg_inter_localClass_351 {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel hF) E d) {s : Y} (hs : s ∈ Subtype.val '' L.muImg c) :
    (Subtype.val '' L.muImg c ∩ LocalClass F s).Nonempty ∧
      IsLocallyHyperoval (LocalClass F s) (Subtype.val '' L.muImg c ∩ LocalClass F s) := by
  obtain ⟨_, ⟨f, hfc, rfl⟩, rfl⟩ := hs
  have hdf : d ∈ LocalClass E f := ⟨hd, f.2.2.1.symm, f.2.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc.1, hfc.2.1.symm, hfc.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f f.2.1
  set pf := Lf.χ ⟨d, hdf⟩
  set qf := Lf.χ ⟨c, hcf⟩
  have hpq : (qf : Y) * pf ≠ pf * qf := fun h => hc.2.1 ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).2 h)
  set N : Set X := muSet E d c ∩ LocalClass E f
  set ψA := (Lf.restrictStar hF ⟨d, hdf⟩).symm
  have hA : imgIn ψA (muSet F pf qf) = N := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      set g := ψA y
      have hy' : (Lf.restrictStar hF ⟨d, hdf⟩ g : Y) = y := by
        rw [Equiv.apply_symm_apply]
      rw [← hy', LocalPoints.restrictStar_val] at hy
      exact ⟨⟨(Lf.mem_localClass_iff hF ⟨d, hdf⟩ ⟨g, g.2.1⟩).2 hy.1,
        (Lf.mem_localClass_iff hF ⟨c, hcf⟩ ⟨g, g.2.1⟩).2 hy.2⟩, g.2.1⟩
    · rintro ⟨⟨hzd, hzc⟩, hzf⟩
      refine ⟨Lf.restrictStar hF ⟨d, hdf⟩ ⟨z, hzf, hzd⟩, ?_, by simp [ψA]⟩
      rw [LocalPoints.restrictStar_val]
      exact ⟨(Lf.mem_localClass_iff hF ⟨d, hdf⟩ ⟨z, hzf⟩).1 hzd,
        (Lf.mem_localClass_iff hF ⟨c, hcf⟩ ⟨z, hzf⟩).1 hzc⟩
  set ψB := L.restrictStar hF f
  have hB : imgIn ψB N = Subtype.val '' L.muImg c ∩ LocalClass F (L.χ f : Y) := by
    ext y
    constructor
    · rintro ⟨g, ⟨⟨-, hgc⟩, -⟩, rfl⟩
      exact ⟨⟨_, ⟨⟨g, g.2.1⟩, hgc, rfl⟩, rfl⟩, (ψB g).2⟩
    · rintro ⟨⟨_, ⟨g, hgc, rfl⟩, rfl⟩, hgf⟩
      have hgf' : (g : X) ∈ LocalClass E f := (L.mem_localClass_iff hF f g).2 hgf
      exact ⟨⟨g, g.2, hgf'⟩, ⟨⟨g.2, hgc⟩, hgf'⟩, rfl⟩
  obtain ⟨hne, hlh⟩ := hMF _ _ pf.2 qf.2 hpq
  rw [← hB]
  constructor
  · rw [← hA]
    obtain ⟨y, hy⟩ := hne
    set y' : LocalClass F (pf : Y) := ⟨y, hy.1⟩
    have h1 : ((ψA y' : _) : X) ∈ imgIn ψA (muSet F pf qf) := ⟨y', hy, rfl⟩
    exact ⟨_, ⟨⟨(ψA y' : X), (ψA y').2.2, (ψA y').2.1⟩, h1, rfl⟩⟩
  · have hinvF : ∀ x ∈ LocalClass F (pf : Y), x * x = 1 := fun x hx => Pair.mul_self hF hx.1
    have hinvE : ∀ x ∈ LocalClass E d ∩ LocalClass E f, x * x = 1 :=
      fun x hx => Pair.mul_self hE hx.1.1
    have h1 := hlh.transport ψA (comm_symm_of_comm _ (Lf.restrictStar_comm hF ⟨d, hdf⟩))
      (tau_symm_of_tau _ (Lf.restrictStar_tau hF hE ⟨d, hdf⟩)) hinvF
    rw [hA, Set.inter_comm (LocalClass E f)] at h1
    exact h1.transport ψB (L.restrictStar_comm hF f) (L.restrictStar_tau hF hE f) hinvE

theorem Pair.isLocally351_muImg {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel hF) E d) : IsLocally351 F (Subtype.val '' L.muImg c) := by
  refine ⟨?_, ?_, fun s hs => (Pair.muImg_inter_localClass_351 hF hE hMF hloc hd hc L hs).1,
    fun s hs => (Pair.muImg_inter_localClass_351 hF hE hMF hloc hd hc L hs).2⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hm : (f : X) * g * f ∈ muSet E d c := Pair.mul_mul_mem_muSet hE ⟨f.2, hf⟩ ⟨g.2, hg⟩
    exact ⟨_, ⟨⟨_, hm.1⟩, hm.2, rfl⟩, congrArg Subtype.val (L.tau f g hm.1)⟩

end Locally351

end CFSG.Fischer
