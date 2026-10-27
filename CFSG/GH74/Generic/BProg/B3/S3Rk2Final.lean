module

public import CFSG.GH74.Generic.BProg.B3.S3Rk2Lemma316
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Main2

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lemma316_of_N {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y)
    (hN : ∀ g ∈ normalizer (A : Set G), g * x = x * g) {g : G} (hgx : g * x * g⁻¹ = x * y) :
    ¬ A.map (MulAut.conj g).toMonoidHom ≤ K ⊔ CxK x K :=
  S3Rk2Lemma316.lemma316_of_N h hN hgx

theorem lemma316 {x a y : G} {K A D J T : Subgroup G} (h306 : Prop306aBarAt x K A)
    (hc : Ctx21 G x K A a D J) (h : Setup30 G x K A y) (_hT : IsZT x y T) {g : G}
    (_hg : g ∈ normalizer (T : Set G) ⊓ centralizer ({y} : Set G)) (hgx : g * x * g⁻¹ = x * y) :
    ¬ A.map (MulAut.conj g).toMonoidHom ≤ K ⊔ CxK x K :=
  lemma316_of_N h (prop312a_of_barAt h306 hc h.shape h.rank1) hgx

end CFSG.GH74.Generic.BProg.B3
