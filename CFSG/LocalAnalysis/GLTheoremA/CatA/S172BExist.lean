module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPos
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPlanar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

private structure RotFacts {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (Bb : Subgroup ↥(orthDerived Q))
    (l : List (V × V)) (p₁ : V × V) (n : ℕ) (y : ↥(orthDerived Q)) : Prop where
  mem : y ∈ Bb
  eq_rot : (y : V ≃ₗ[ZMod 2] V) = rot Q p₁.1 p₁.2
  mem_torus : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l
  pow_three : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1
  mem_orth : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  orderOf_eq : orderOf y = 3
  fixedSpace_eq : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p₁
  finrank_fixed : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * (n - 1)
  layer_eq : GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) =
      (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q)
  support_le : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q
  layer : LayerIs 3 (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) (isOmMA (n - 1) 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private lemma exists_rotData (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hn : 7 ≤ n) {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    (hF : FrameOf Q Bb (n - 1) l) {p₁ : V × V} (hp₁ : p₁ ∈ l) :
    ∃ y : ↥(orthDerived Q), RotFacts Q Bb l p₁ n y := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl := hF.isFrame
  have hpp₁ := hl.pair p₁ hp₁
  obtain ⟨y, hyBb, hyrot⟩ := hF.exists_mem_rot hp₁
  have hyt : (y : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hyBb
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := torus_pow_three hl _ hyt
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy1 : y ≠ 1 := by
    intro h
    apply rot_ne_one hpp₁
    rw [← hyrot, h]
    rfl
  have hy3 : orderOf y = 3 := orderOf_eq_prime (Subtype.ext (by simpa using hy3')) hy1
  have hyfix : fixedSpace (y : V ≃ₗ[ZMod 2] V) = perpPlane Q p₁ := by
    rw [hyrot]
    refine fixedSpace_eq_perpPlane hl hp₁ (rot_mem_torus hp₁) ?_
      (fun p hp hne => rot_apply_left_of_ne hl hp₁ hp (Ne.symm hne))
    rw [rot_apply_left hpp₁]
    exact hpp₁.ne.symm
  have hyfin : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * (n - 1) := by
    rw [hyfix, finrank_perpPlane hQ hpp₁]
    omega
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) := by
    rw [hyfix]
    exact not_isPlusType_comp_perpPlane hQ hplus hpp₁
  obtain ⟨hlayer, hLy⟩ :=
    layerIs_centralizer_planar hQ hy3 (m := n - 1) (by omega) (by omega) hyfin hminus
  have hx := oddOrderIsometry_three hQ hyO hy3'
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  exact ⟨y, ⟨hyBb, hyrot, hyt, hy3', hyO, hy3, hyfix, hyfin, hlayer, hAΩ, hLy⟩⟩

private lemma rotData_notMem_zpowers {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    {p₁ : V × V} {n : ℕ} {y : ↥(orthDerived Q)} (hF : FrameOf Q Bb (n - 1) l)
    (RF : RotFacts Q Bb l p₁ n y) {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hfull : ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1)
    {p₂ : V × V} (hp₁ : p₁ ∈ l) (hp₂ : p₂ ∈ l) (hp₁₂ : p₁ ≠ p₂) :
    y ∉ Subgroup.zpowers d := by
  have hl := hF.isFrame
  have hpp₁ := hl.pair p₁ hp₁
  intro hmem
  have hmem' := coe_mem_zpowers_of_mem (K := orthDerived Q) hmem
  refine not_mem_zpowers_of_apply_ne (G := V ≃ₗ[ZMod 2] V) (X := V) (x := p₂.1)
    (torus_pow_three hl _ (hF.mem_torus hd)) (hfull p₂ hp₂) ?_ ?_ hmem'
  · rw [RF.eq_rot]
    exact rot_ne_one hpp₁
  · rw [RF.eq_rot]
    exact rot_apply_left_of_ne hl hp₁ hp₂ hp₁₂

private lemma rotData_centralizer_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)} {p₁ : V × V} {n : ℕ}
    {y : ↥(orthDerived Q)} (hF : FrameOf Q Bb (n - 1) l) (hp₁ : p₁ ∈ l) (hn : 7 ≤ n)
    (RF : RotFacts Q Bb l p₁ n y) :
    Bb ⊓ Subgroup.centralizer
        (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers y := by
  have hl := hF.isFrame
  rw [RF.layer_eq]
  apply le_antisymm
  · intro b hb'
    obtain ⟨hbBb, hbc⟩ := Subgroup.mem_inf.1 hb'
    have hbt : (b : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hbBb
    have hbcy : b ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (torus_commute hl hbt RF.mem_torus).eq)
    have hschur := apply_eq_of_commute_supportedFixedDerived hQ RF.mem_orth RF.pow_three
      (by rw [RF.finrank_fixed]; omega)
      (mem_isometryCentralizer_of_mem_centralizer hbcy) (fun g hg => by
        have hgm : (⟨g, RF.support_le hg⟩ : ↥(orthDerived Q)) ∈
            (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) :=
          Subgroup.mem_subgroupOf.2 hg
        exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hbc _ hgm)).symm)
    have hmem := mem_zpowers_rot_of_fixes_perpPlane hl hp₁ hbt (fun w hw => hschur w (by
      rw [RF.fixedSpace_eq]
      exact hw))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, RF.eq_rot]
    exact hk
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨RF.mem, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgc : g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
      mem_centralizer_of_mem_isometryCentralizer
        (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
    exact Subgroup.mem_centralizer_singleton_iff.1 hgc

private lemma rotData_pair_layer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) {Bb : Subgroup ↥(orthDerived Q)}
    {l : List (V × V)} {p₁ : V × V} (hF : FrameOf Q Bb (n - 1) l) (hp₁ : p₁ ∈ l)
    (hn : 7 ≤ n) {y : ↥(orthDerived Q)} (RF : RotFacts Q Bb l p₁ n y)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hfull : ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1)
    {p₂ : V × V} (hp₂ : p₂ ∈ l) (hp₁₂ : p₁ ≠ p₂) :
    LayerIs 3 (Subgroup.centralizer ({d, y} : Set ↥(orthDerived Q))) (isUnA (n - 2) 2) := by
  have hl := hF.isFrame
  obtain ⟨j, _, hj2, hj3, hj4⟩ := exists_pair_adjust hl hp₁ (hF.mem_torus hd) hfull
  set d₂ : ↥(orthDerived Q) := d * y ^ j with hd₂
  have hd₂c : (d₂ : V ≃ₗ[ZMod 2] V) = (d : V ≃ₗ[ZMod 2] V) * rot Q p₁.1 p₁.2 ^ j := by
    rw [hd₂, Subgroup.coe_mul, Subgroup.coe_pow, RF.eq_rot]
  have hd₂t : (d₂ : V ≃ₗ[ZMod 2] V) ∈ torus Q l :=
    hF.mem_torus (Bb.mul_mem hd (Bb.pow_mem RF.mem j))
  have hd₂3 : orderOf d₂ = 3 := orderOf_eq_prime (Subtype.ext (by
    simpa using torus_pow_three hl _ hd₂t))
    (fun h => hj2 p₂ hp₂ hp₁₂.symm (by rw [← hd₂c, h]; rfl))
  have hd₂A : (d₂ : V ≃ₗ[ZMod 2] V) ∈ supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) :=
    mem_supportedFixedDerived_of_fixes hQ RF.mem_orth RF.pow_three
      (by rw [RF.finrank_fixed]; omega)
      (orthDerived_le_orthogonalGroup d₂.2) (torus_pow_three hl _ hd₂t)
      (torus_commute hl hd₂t RF.mem_torus).eq (fun v hv => by
        rw [hd₂c]
        rw [RF.eq_rot] at hv
        exact hj4 v hv)
  have hcom : finrank (ZMod 2) ↥(fixedSpace (d₂ : V ≃ₗ[ZMod 2] V) ⊓
      fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 := by
    rw [hd₂c, RF.eq_rot, hj3]
    exact finrank_perpL_eq_two hl hdim hF.length_eq (by omega)
  have hLdy := layerIs_centralizer_pair_planar hQ RF.orderOf_eq (m := n - 1) (by omega)
    (by omega) RF.finrank_fixed hd₂A hd₂3 hcom
  have hpair : Subgroup.centralizer ({d₂, y} : Set ↥(orthDerived Q)) =
      Subgroup.centralizer ({d, y} : Set ↥(orthDerived Q)) := by
    have := centralizer_pair_eq_of_mul_zpow d y (j : ℤ)
    rwa [zpow_natCast] at this
  rw [hpair, show n - 1 - 1 = n - 2 by omega] at hLdy
  exact hLdy

theorem modelExist_orthDerived {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hbound : ∀ E : Subgroup ↥(orthDerived Q), CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ (n - 1))
    (hn : 7 ≤ n) (_hodd : Odd n) (hb : CatDistinct.OrderBridge) :
    ModelExist 3 ↥(orthDerived Q) (n - 1) (isUnA (n - 1) 2) (isOmMA (n - 1) 2)
      (isUnA (n - 2) 2) := by
  intro Bb hBb hcard d hd hLd hcd
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, hF⟩ := exists_frame_of_card hQ hbound hBb hcard
  have hl := hF.isFrame
  have hfull := fullSupport_of_layerIs hQ hdim hplus (by omega) hb hF hd hLd hcd
  have hlen : 2 ≤ l.length := by rw [hF.length_eq]; omega
  obtain ⟨p₁, hp₁, p₂, hp₂, hp₁₂⟩ := exists_mem_ne_of_two_le_length hl hlen
  obtain ⟨y, RF⟩ := exists_rotData hQ hdim hplus hn hF hp₁
  have hydn := rotData_notMem_zpowers hF RF hd hfull hp₁ hp₂ hp₁₂
  have hyc := rotData_centralizer_eq hQ hF hp₁ hn RF
  have hLdy := rotData_pair_layer hQ hdim hF hp₁ hn RF hd hfull hp₂ hp₁₂
  exact ⟨y, RF.mem, hydn, RF.layer, hyc, hLdy⟩

end CFSG.LocalAnalysis.GLTheoremA.S172B

end