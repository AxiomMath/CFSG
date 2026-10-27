module

public import CFSG.GH74.Generic.S1.Front
public import CFSG.GH74.Generic.S1.FrameMain
public import CFSG.GH74.Generic.JMaxThin
public import CFSG.GH74.L5U5.IdentUnitary

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.GH74.Generic

structure S1Setup (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) :
    Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ Open.twoRank G
  gen4 : Gen4 G
  kgh : KGH G
  sylow : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)
  layerNe : ∃ x : G, orderOf x = 2 ∧ layerBar x ≠ ⊥
  inv : orderOf x = 2
  comp : IsComponent K
  shape : ShapeS1 x K
  jmax : IsJMax x K
  nothin : ¬ GLS.HasTwoThinConfiguration G

section A4

variable {G : Type} [Group G]

@[expose] def WeakCTA4 (F : Type) [Field F] [Finite F] (J : Fin 4 → Subgroup G) : Prop :=
  (∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ J i, ∀ b ∈ J j, a * b = b * a) ∧
    ∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (J i) (J j)

@[expose] def WeakPhanA4 (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
    (J : Fin 4 → Subgroup G) : Prop :=
  (∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ J i, ∀ b ∈ J j, a * b = b * a) ∧
    ∀ i j : Fin 4, (j : ℕ) = i + 1 → ∃ W, UnitaryBlockStandardPair F p f W (J i) (J j)

end A4

section Nbhd

variable {G : Type} [Group G] [Finite G]

@[expose] def S1LinkedLin (x : G) (K : Subgroup (CentralizerBar x)) (F : Type) [Field F] [Finite F]
    (J : Fin 4 → Subgroup G) : Prop :=
  ∃ (U : Fin 3 → Subgroup ↥K) (W : Fin 3 → Fin 3 → Subgroup ↥K), WeakCTSystem F 3 U W ∧
    ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G) ∧
      ((J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = (U i).map K.subtype

@[expose] def S1LinkedUni (x : G) (K : Subgroup (CentralizerBar x)) (F : Type) [Field F] [Finite F]
    (p f : ℕ) [Fact p.Prime] [CharP F p] (J : Fin 4 → Subgroup G) : Prop :=
  ∃ (U : Fin 3 → Subgroup ↥K) (W : Fin 3 → Fin 3 → Subgroup ↥K), WeakPhanA F p f 3 U W ∧
    ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G) ∧
      ((J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = (U i).map K.subtype

@[expose] def S1NormalizerProp (x : G) (J : Fin 4 → Subgroup G) : Prop :=
  ∃ y : G, y ∈ J 1 ∧ orderOf y = 2 ∧ (∀ a ∈ J 1, a * y = y * a) ∧
    ∀ Q : Subgroup G, Q ≠ ⊥ → Q ≤ Subgroup.closure {x, y} →
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer ((⨆ i, J i : Subgroup G) : Set G)

@[expose] def IsS1A4 (x : G) (K : Subgroup (CentralizerBar x)) (J : Fin 4 → Subgroup G) : Prop :=
  ((∃ (p f : ℕ) (F : Type) (_ : Field F) (_ : Finite F), p.Prime ∧ Nat.card F = p ^ f ∧
      3 ≤ p ^ f ∧ WeakCTA4 F J ∧ S1LinkedLin x K F J) ∨
    (∃ (p f : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : Fact p.Prime) (_ : CharP F p),
      Nat.card F = (p ^ f) ^ 2 ∧ 5 ≤ p ^ f ∧ WeakPhanA4 F p f J ∧ S1LinkedUni x K F p f J)) ∧
    S1NormalizerProp x J

end Nbhd

@[expose] def S1ExoticExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (v : G) (hv : v ∈ centralizer ({x} : Set G)), IsConj x v → v ≠ x → v * v = 1 →
      barOf hv ∉ K → ∀ α : MulAut ↥K,
        (∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹) →
          IsGraphAut α → ¬ GoodFixedCentral (ThreeModel ↥K) α → False

@[expose] def S1Nbhd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J

@[expose] def S1LevelE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    ∀ J : Fin 4 → Subgroup G, IsS1A4 x K J → ⨆ i, J i = ⊤

theorem catalog_of_isS1A4 {G : Type} [Group G] [Finite G] {x : G}
    {K : Subgroup (CentralizerBar x)} {J : Fin 4 → Subgroup G} (h : IsS1A4 x K J)
    (hgen : ⨆ i, J i = ⊤) (hs : IsSimpleGroup G) : Catalog G := by
  rcases h.1 with ⟨p, f, F, _, _, hp, hF, hq, hW, -⟩ | ⟨p, f, F, _, _, _, _, hF, hq, hW, -⟩
  · exact lieModel_catalog G .PSL 5 p f
      (lieModel_A4_of_iSup_eq_top p f hp hF hq J hW.1 hW.2 hgen hs)
  · exact lieModel_catalog G .PSU 5 p f
      (lieModel_A4_unitary_of_iSup_eq_top F p f hF hq J hW.1 hW.2 hgen hs)

theorem s1_shapeCase_of_props (hB4 : S1OuterClassification) (hExo : S1ExoticExcluded)
    (hNbhd : S1Nbhd) (hE : S1LevelE) : S_shapeCaseMaxNT @ShapeS1 := by
  intro G _ _ hs hn hr hgen hK hnab hL x hx K hKc _ hP
  obtain ⟨hthin, hmax, hsh⟩ := hP
  have hset : S1Setup G x K := ⟨hs, hn, hr, hgen, hK, hnab, hL, hx, hKc, hsh, hmax, hthin⟩
  obtain ⟨hfront, v, hv, hconj, hvx, hv2, hvbK, α, hα, hnotA, hRG⟩ :=
    s1_front hB4 hs hn hgen hx hKc hsh
  rcases hRG with hR | hGr
  · have : K.Normal := normal_of_layer_eq hfront.layer_eq
    obtain ⟨u, hu, hframe⟩ := s1_frame hx hsh.2 hv hconj hv2 hvbK hα hR
    obtain ⟨J, hJ⟩ := hNbhd G x K hset hfront u hu hframe
    exact catalog_of_isS1A4 hJ (hE G x K hset J hJ) hs
  · exact (hExo G x K hset hfront v hv hconj hvx hv2 hvbK α hα hGr hnotA).elim

end CFSG.GH74.Generic.S1
