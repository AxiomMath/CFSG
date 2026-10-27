module

public import CFSG.GH74.Generic.S1.Defs
public import CFSG.GH74.Generic.Front.DataStatement
public import CFSG.GH74.Generic.Front.FrontShapes
public import CFSG.GH74.Generic.Front.OuterThree
public import CFSG.GH74.Generic.Shapes

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] [Finite G]

theorem false_of_goodFixed {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    (hSch : ∀ P : Subgroup (CentralizerBar x), GoodSub (ThreeModel ↥K) P → P ≤ K)
    (hB5 : NoNoncentralInvolutionConj x K) {v : G} (hv : v ∈ centralizer ({x} : Set G))
    (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1) (H : Subgroup (CentralizerBar x))
    (hHle : H ≤ K ⊓ centralizer ({barOf hv} : Set (CentralizerBar x))) (hHz : xbar x ∈ H)
    (hHgood : GoodSub (ThreeModel ↥K) H) : False := by
  obtain ⟨c, hc'⟩ := isConj_iff.1 hconj
  obtain ⟨U, hU⟩ : ∃ U : ↥(centralizer ({x} : Set G)), U = ⟨v, hv⟩ := ⟨_, rfl⟩
  have hU2 : U * U = 1 := by rw [hU]; exact Subtype.ext hv2
  have hc : c⁻¹ * (U : G) * c = x := by
    rw [hU]
    show c⁻¹ * v * c = x
    rw [← hc']
    group
  have hbar : barOf hv = proj x U := by rw [hU]; rfl
  have hHc : ∀ h ∈ H, h * proj x U = proj x U * h := fun h hh => by
    rw [← hbar]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hHle hh).2
  have hxcent : (xH x : ↥(centralizer ({x} : Set G))) ∈ CU x U :=
    Subgroup.mem_centralizer_singleton_iff.2 (xH_central x U).symm
  have hxH : proj x (xH x) ∈ H := hHz
  have hres := transfer_bar x U hU2 hc (ThreeModel ↥K) K hSch H hHgood hHc ⟨xH x, hxcent⟩ hxH
    ⟨1, by rw [pow_one, pow_two]; exact xH_mul_self hx⟩
  obtain ⟨x2, hx2⟩ : ∃ x2 : ↥(centralizer ({x} : Set G)),
      x2 = transportC x U hc ⟨xH x, hxcent⟩ := ⟨_, rfl⟩
  have hx2val : (x2 : G) = c⁻¹ * x * c := by rw [hx2]; rfl
  have hx2sq : x2 * x2 = 1 := by
    have h1 : (⟨xH x, hxcent⟩ : ↥(CU x U)) * ⟨xH x, hxcent⟩ = 1 :=
      Subtype.ext (xH_mul_self hx)
    rw [hx2, ← map_mul, h1, map_one]
  have hbK : proj x x2 ∈ K := by rw [hx2]; exact hres
  have hne : proj x x2 ≠ xbar x := by
    intro h
    have hn' : x2⁻¹ * xH x ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) :=
      (QuotientGroup.eq).1 h
    have hcomm : x2 * xH x = xH x * x2 := xH_central x x2
    have hsq : (x2⁻¹ * xH x) * (x2⁻¹ * xH x) = 1 := by
      have h1 : xH x * x2⁻¹ = x2⁻¹ * xH x := by
        have := congrArg (fun z => x2⁻¹ * z * x2⁻¹) hcomm
        simpa [mul_assoc] using this
      calc (x2⁻¹ * xH x) * (x2⁻¹ * xH x) = x2⁻¹ * (xH x * x2⁻¹) * xH x := by group
        _ = x2⁻¹ * (x2⁻¹ * xH x) * xH x := by rw [h1]
        _ = (x2 * x2)⁻¹ * (xH x * xH x) := by group
        _ = 1 := by rw [hx2sq, xH_mul_self hx]; group
    have hP : IsPGroup 2 (zpowers (x2⁻¹ * xH x)) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hsq)
    have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP (Subgroup.mem_zpowers _) hn'
    have h2 : x2 = xH x := by
      have := congrArg (fun z => x2 * z) h1
      simpa using this.symm
    have h3 : c⁻¹ * x * c = x := by
      rw [← hx2val, h2]
      rfl
    apply hvx
    rw [← hc']
    have h4 : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [h3] at h4
    exact h4.symm
  exact hB5 (x2 : G) x2.2 (congrArg Subtype.val hx2sq) hbK hne
    (isConj_iff.2 ⟨c⁻¹, by rw [hx2val]; group⟩)

theorem map_subtype_le_centralizer {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {u : X}
    (H : Subgroup ↥K) (hfix : ∀ h ∈ H, (MulAut.conjNormal u : MulAut ↥K) h = h) :
    H.map K.subtype ≤ K ⊓ centralizer ({u} : Set X) := by
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨h.2, ?_⟩
  change (h : X) ∈ Subgroup.centralizer ({u} : Set X)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := congrArg (fun k : ↥K => (k : X)) (hfix h hh)
  simp only [MulAut.conjNormal_apply] at h1
  change (h : X) * u = u * (h : X)
  calc (h : X) * u = (u * (h : X) * u⁻¹) * u := by rw [h1]
    _ = u * (h : X) := by group

structure S1Front (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop where
  layer_eq : layer (CentralizerBar x) = K
  cent_eq : centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x)
  b5 : NoNoncentralInvolutionConj x K
  good_le : ∀ P : Subgroup (CentralizerBar x), GoodSub (ThreeModel ↥K) P → P ≤ K

theorem s1_front (hB4 : S1OuterClassification) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) (hsh : ShapeS1 x K) :
    S1Front G x K ∧
      ∃ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v ∧ v ≠ x ∧ v * v = 1 ∧
        barOf hv ∉ K ∧
        ∃ α : MulAut ↥K, (∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹) ∧
          ¬ GoodFixedCentral (ThreeModel ↥K) α ∧ (IsReflectionAut α ∨ IsGraphAut α) := by
  obtain ⟨hK1, -⟩ := hsh
  have hmodel : ShapeModel ↥K := Or.inl hK1
  obtain ⟨hxK', hlayer, hcentK, -, -, -, -, -, hB5, v, hv, hconj, hvx, hv2, hvb1, hvbx, hvbK⟩ :=
    generic_front_end_full frontDataStatement (outerStatement_of_three outerThreeStatement) hs hn
      hgen hx hKc hmodel
  have hKn : K.Normal := normal_of_layer_eq hlayer
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hcentK]
    exact (Subgroup.zpowers_le).2 hxK'
  have hSch := goodSub_le_of_outerStatement (outerStatement_of_three outerThreeStatement) K hmodel
    hcentle
  have hbar2 : barOf hv * barOf hv = 1 := by
    have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
      rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2,
        map_one]
    rwa [map_mul] at this
  have hα2 : (MulAut.conjNormal (barOf hv) : MulAut ↥K) * MulAut.conjNormal (barOf hv) = 1 := by
    rw [← map_mul, hbar2, map_one]
  have hout : ∀ k : ↥K, (MulAut.conjNormal (barOf hv) : MulAut ↥K) ≠ MulAut.conj k := fun k h =>
    hvbK (mem_of_conjNormal_inner hcentle h)
  refine ⟨⟨hlayer, hcentK, hB5, hSch⟩, v, hv, hconj, hvx, hv2, hvbK, MulAut.conjNormal (barOf hv),
    fun k => by simp [MulAut.conjNormal_apply], ?_⟩
  rcases hB4 ↥K hK1 _ hα2 hout with hA | hR | hGr
  · exfalso
    obtain ⟨H, hfix, hz, hgood⟩ := hA
    refine false_of_goodFixed hx hSch hB5 hv hconj hvx hv2 (H.map K.subtype)
      (map_subtype_le_centralizer H hfix) ?_ (goodSub_map K.subtype hgood)
    refine ⟨⟨xbar x, hxK'⟩, hz _ ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  · refine ⟨fun hA => ?_, Or.inl hR⟩
    obtain ⟨H, hfix, hz, hgood⟩ := hA
    refine false_of_goodFixed hx hSch hB5 hv hconj hvx hv2 (H.map K.subtype)
      (map_subtype_le_centralizer H hfix) ?_ (goodSub_map K.subtype hgood)
    refine ⟨⟨xbar x, hxK'⟩, hz _ ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  · refine ⟨fun hA => ?_, Or.inr hGr⟩
    obtain ⟨H, hfix, hz, hgood⟩ := hA
    refine false_of_goodFixed hx hSch hB5 hv hconj hvx hv2 (H.map K.subtype)
      (map_subtype_le_centralizer H hfix) ?_ (goodSub_map K.subtype hgood)
    refine ⟨⟨xbar x, hxK'⟩, hz _ ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))

end CFSG.GH74.Generic.S1
