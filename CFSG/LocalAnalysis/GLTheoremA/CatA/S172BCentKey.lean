module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem rot_apply_left_of_ne {l : List (V × V)} (hl : IsFrame Q l) {p q : V × V} (hp : p ∈ l)
    (hq : q ∈ l) (hne : p ≠ q) : rot Q p.1 p.2 q.1 = q.1 := by
  obtain ⟨h1, -, h3, -⟩ := hl.perp_of_mem_of_ne hp hq hne
  exact rot_apply_of_perp (hl.pair p hp) (by rw [polar_comm]; exact h1) (by rw [polar_comm]; exact h3)

theorem rot_ne_one {p : V × V} (hp : MinusPair Q p.1 p.2) : rot Q p.1 p.2 ≠ 1 := by
  intro h
  have := rot_apply_left hp
  rw [h] at this
  exact hp.ne this

private lemma rot_mem_zpowers_of_centralizes {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} {m : ℕ}
    (hF : FrameOf Q Bb m l) {d : ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    {p : V × V} (hp : p ∈ l)
    (hcomm : ∀ g ∈ GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))),
      Commute (g : V ≃ₗ[ZMod 2] V) (rot Q p.1 p.2)) :
    rot Q p.1 p.2 ∈ Subgroup.zpowers (d : V ≃ₗ[ZMod 2] V) := by
  obtain ⟨r, hrBb, hr⟩ := hF.exists_mem_rot hp
  have hrc : r ∈ Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) := by
    refine Subgroup.mem_inf.2 ⟨hrBb, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hr]
    exact (hcomm g hg).eq
  rw [hcd] at hrc
  rw [← hr]
  exact coe_mem_zpowers_of_mem hrc

private lemma rot_mem_zpowers_of_specialBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} {m : ℕ} (hF : FrameOf Q Bb m l)
    {d : ↥(orthDerived Q)} (hdO : (d : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hd3' : (d : V ≃ₗ[ZMod 2] V) ^ 3 = 1)
    (hcd : Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    (hl : IsFrame Q l) (hdt : (d : V ≃ₗ[ZMod 2] V) ∈ torus Q l)
    (hLeq : GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
      (specialBlock Q (d : V ≃ₗ[ZMod 2] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))
    {p : V × V} (hp : p ∈ l) (hfix : (d : V ≃ₗ[ZMod 2] V) p.1 = p.1) :
    rot Q p.1 p.2 ∈ Subgroup.zpowers (d : V ≃ₗ[ZMod 2] V) := by
  refine rot_mem_zpowers_of_centralizes hF hcd hp fun g hg => ?_
  have hgs : (g : V ≃ₗ[ZMod 2] V) ∈ specialBlock Q (d : V ≃ₗ[ZMod 2] V) (X ^ 2 + X + 1) := by
    rw [hLeq] at hg
    exact Subgroup.mem_subgroupOf.1 hg
  have hfix2 : (d : V ≃ₗ[ZMod 2] V) p.2 = p.2 :=
    fixes_planeSpan_of_apply_left hl hp hdt hfix p.2 (right_mem_planeSpan p)
  exact commute_rot_of_fix (orthDerived_le_orthogonalGroup g.2)
    (apply_eq_of_mem_specialBlock hQ hdO hd3' hgs hfix)
    (apply_eq_of_mem_specialBlock hQ hdO hd3' hgs hfix2)

private lemma rot_mem_zpowers_of_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} {m : ℕ} (hF : FrameOf Q Bb m l)
    {d : ↥(orthDerived Q)} (hdO : (d : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hd3' : (d : V ≃ₗ[ZMod 2] V) ^ 3 = 1)
    (hcd : Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    (hl : IsFrame Q l) (hdt : (d : V ≃ₗ[ZMod 2] V) ∈ torus Q l)
    {F : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hLeq : GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
      F.subgroupOf (orthDerived Q))
    (hFle : F ≤ supportedFixedDerived Q (d : V ≃ₗ[ZMod 2] V))
    {p : V × V} (hp : p ∈ l) (hmov : (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1) :
    rot Q p.1 p.2 ∈ Subgroup.zpowers (d : V ≃ₗ[ZMod 2] V) := by
  refine rot_mem_zpowers_of_centralizes hF hcd hp fun g hg => ?_
  have hgS : (g : V ≃ₗ[ZMod 2] V) ∈ supportedFixedDerived Q (d : V ≃ₗ[ZMod 2] V) := by
    rw [hLeq] at hg
    exact hFle (Subgroup.mem_subgroupOf.1 hg)
  exact commute_rot_of_fix (orthDerived_le_orthogonalGroup g.2)
    (apply_eq_of_mem_supportedFixedDerived hQ hdO hd3' hgS
      (apply_sq_add_apply_add_self_of_apply_left_ne hl hp hdt hmov p.1 (left_mem_planeSpan p)))
    (apply_eq_of_mem_supportedFixedDerived hQ hdO hd3' hgS
      (apply_sq_add_apply_add_self_of_apply_left_ne hl hp hdt hmov p.2 (right_mem_planeSpan p)))

private lemma false_of_layerIs_top (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hn : 5 ≤ n) (hb : CatDistinct.OrderBridge) {d : ↥(orthDerived Q)} (hd1 : d = 1)
    (hLd : LayerIs 3 (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) (isUnA (n - 1) 2)) : False := by
  subst hd1
  apply not_layerIs_top_isUnA hQ hdim hplus hn hb
  have : Subgroup.centralizer ({1} : Set ↥(orthDerived Q)) = ⊤ := by simp
  rw [this] at hLd
  exact hLd

private lemma false_of_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) (hn : 5 ≤ n)
    (hb : CatDistinct.OrderBridge) {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    (hF : FrameOf Q Bb (n - 1) l) {d : ↥(orthDerived Q)} (hd3 : orderOf d = 3) (hd : d ∈ Bb)
    {F : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hLd : LayerIs 3 (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) (isUnA (n - 1) 2))
    (hLeq : GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
      F.subgroupOf (orthDerived Q))
    (hFle : F ≤ supportedFixedDerived Q (d : V ≃ₗ[ZMod 2] V))
    (hFdim : finrank (ZMod 2) (fixedSpace (d : V ≃ₗ[ZMod 2] V)) ≤ 4 ∨
      F = supportedFixedDerived Q (d : V ≃ₗ[ZMod 2] V))
    {p₀ : V × V} (hp₀ : p₀ ∈ l) (hmov₀ : (d : V ≃ₗ[ZMod 2] V) p₀.1 ≠ p₀.1)
    (huniq : ∀ p ∈ l, p ≠ p₀ → (d : V ≃ₗ[ZMod 2] V) p.1 = p.1) : False := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hl := hF.isFrame
  have hdt : (d : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hd
  have hfs := fixedSpace_eq_perpPlane hl hp₀ hdt hmov₀ huniq
  have hfsdim : finrank (ZMod 2) (fixedSpace (d : V ≃ₗ[ZMod 2] V)) = 2 * (n - 1) := by
    rw [hfs, finrank_perpPlane hQ (hl.pair p₀ hp₀), hdim]
    omega
  have hFeq : F = supportedFixedDerived Q (d : V ≃ₗ[ZMod 2] V) := hFdim.resolve_left (by omega)
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (d : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hfs]
    exact not_isPlusType_comp_perpPlane hQ hplus (hl.pair p₀ hp₀)
  have h1 : catalogIs (PSimple 3 (GLALayer (Subgroup.centralizer {d}))) (isUnA (n - 1) 2) := hLd.2
  have h2 := catalogIs_pSimple_supportedFixedDerived_minus hQ hd3 (m := n - 1) (by omega)
    hfsdim hminus
  rw [hLeq, hFeq] at h1
  exact false_of_catalogIs_isUnA_isOmMA hb h1 h2

theorem fullSupport_of_layerIs (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) (hn : 5 ≤ n)
    (hb : CatDistinct.OrderBridge) {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    (hF : FrameOf Q Bb (n - 1) l) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hLd : LayerIs 3 (Subgroup.centralizer {d}) (isUnA (n - 1) 2))
    (hcd : Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) = Subgroup.zpowers d) :
    ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1 := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hdt : (d : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hd
  have hd3' : (d : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hdt
  have hdO : (d : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup d.2
  by_cases hd1 : d = 1
  · exfalso
    exact false_of_layerIs_top hQ hdim hplus hn hb hd1 hLd
  have hd3 : orderOf d = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hd3')) hd1
  rcases comp_cases_orthDerived hQ hd3 hLd.1 with ⟨-, -, hLeq⟩ | ⟨F, -, hFle, -, hFdim, hLeq⟩
  · intro p hp hfix
    have hmem := rot_mem_zpowers_of_specialBlock hQ hF hdO hd3' hcd hl hdt hLeq hp hfix
    refine not_mem_zpowers_of_apply_eq (G := V ≃ₗ[ZMod 2] V) (X := V) (x := p.1) hfix ?_ hmem
    show rot Q p.1 p.2 p.1 ≠ p.1
    rw [rot_apply_left (hl.pair p hp)]
    exact (hl.pair p hp).ne.symm
  · exfalso
    obtain ⟨p₀, hp₀, hmov₀⟩ : ∃ p₀ ∈ l, (d : V ≃ₗ[ZMod 2] V) p₀.1 ≠ p₀.1 := by
      by_contra hno
      push Not at hno
      exact hd1 (Subtype.ext (eq_one_of_forall_apply_left hl hdt hno))
    have hrot : ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1 →
        rot Q p.1 p.2 ∈ Subgroup.zpowers (d : V ≃ₗ[ZMod 2] V) :=
      fun p hp hmov => rot_mem_zpowers_of_supportedFixedDerived hQ hF hdO hd3' hcd hl hdt hLeq hFle hp hmov
    have huniq : ∀ p ∈ l, p ≠ p₀ → (d : V ≃ₗ[ZMod 2] V) p.1 = p.1 := by
      intro p hp hne
      by_contra hmov
      exact not_mem_zpowers_of_apply_ne (G := V ≃ₗ[ZMod 2] V) (X := V) (x := p₀.1) hd3' hmov₀
        (rot_ne_one (hl.pair p hp)) (rot_apply_left_of_ne hl hp hp₀ hne) (hrot p hp hmov)
    exact false_of_supportedFixedDerived hQ hdim hplus hn hb hF hd3 hd hLd hLeq hFle hFdim hp₀ hmov₀ huniq

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
