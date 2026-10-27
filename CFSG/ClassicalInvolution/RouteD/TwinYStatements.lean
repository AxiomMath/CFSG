module

public import CFSG.ClassicalInvolution.RouteD.TwinYSetup
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsTD
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsD
public import CFSG.ClassicalInvolution.RouteD.TwinYExistsB
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD

local notation "𝒞" => CoreAssembly.conjClass

@[expose] def TwinRow (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeTwinD 2 t n ∨ ShapeTwinSL4 2 t n ∨ ShapeTwinB 2 t n ∨ ShapeTwinSp2 2 t n ∨
    ShapeTwinTD 2 t n ∨ ShapeTwinSU4 2 t n

@[expose] def twinYModel (q : ℕ) (t : StatedLieTag) (n : ℕ) : StatedLieTag × ℕ :=
  match t with
  | .POmegaPlus => (if q % 4 = 1 then .POmegaPlus else .POmegaMinus, n + 1)
  | .POmegaMinus => (if q % 4 = 1 then .POmegaMinus else .POmegaPlus, n + 1)
  | .POmegaOdd => (.POmegaOdd, n + 1)
  | .PSp => (.POmegaOdd, n + 1)
  | .PSU => (if q % 4 = 1 then .POmegaMinus else .POmegaPlus, n)
  | .PSL => (if q % 4 = 1 then .POmegaPlus else .POmegaMinus, n)
  | _ => (t, n)

section Twin

variable {G : Type} [Group G]

structure IsTwinAt (Ω : Set (Subgroup G)) (K T : Subgroup G) (z : G) : Prop where
  mem : T ∈ centralizingMembers Ω {z}
  ne : T ≠ K
  comm_T : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T → Commutes T N
  comm_K : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N

theorem isTwinAt_of_ctx [Finite G] {p f : ℕ} [Fact p.Prime] {tY : StatedLieTag} {nY : ℕ}
    {Ω : Set (Subgroup G)} {K T : Subgroup G} {z : G} (c : TCtx p f tY nY Ω K z)
    (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁) : IsTwinAt Ω K T z where
  mem := hT
  ne := c.twin_ne hT hTQ
  comm_T := fun _ hN hNT => c.commutes_T_of_ne hT hTQ hN hNT
  comm_K := fun _ hN hNK => c.commutes_K_of_ne hN hNK

theorem exists_isTwinAt_of_ctx [Finite G] {p f : ℕ} [Fact p.Prime] {tY : StatedLieTag} {nY : ℕ}
    {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} (c : TCtx p f tY nY Ω K z) :
    ∃ T, IsTwinAt Ω K T z := by
  obtain ⟨T, hT, hTQ⟩ := c.exists_twin
  exact ⟨T, isTwinAt_of_ctx c hT hTQ.le⟩

end Twin

section Statements

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYP1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      LocalShapeT p f 2 t n (𝒞 K) z → ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z →
        IsClassicalMember p f T z → ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u}

@[expose] def TwinYType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      LocalShapeT p f 2 t n (𝒞 K) z → ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z →
        IsClassicalMember p f T z → ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u} →
          LocalShapeT p f 0 (twinYModel (p ^ f) t n).1 (twinYModel (p ^ f) t n).2 (𝒞 K) e.u

variable {p f}

structure TwinYConfig (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K T : Subgroup G) (z : G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G)
    (e' : TwinElt J J' w) (β : Subgroup G) (s : G) : Prop where
  twin : IsTwinAt Ω K T z
  clsT : IsClassicalMember p f T z
  mem_J : J ∈ centralizingMembers Ω {z}
  mem_J' : J' ∈ centralizingMembers Ω {z}
  J_ne_K : J ≠ K
  J_ne_T : J ≠ T
  J'_ne_K : J' ≠ K
  J'_ne_T : J' ≠ T
  twinJ : IsTwinAt Ω J J' w
  clsJ : IsClassicalMember p f J w
  clsJ' : IsClassicalMember p f J' w
  memβ : β ∈ centralizingMembers Ω {e'.u}
  clsβ : IsClassicalMember p f β s
  linear : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β
  comm_u : s * e.u = e.u * s

variable (p f)

@[expose] def TwinYPartner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      LocalShapeT p f 2 t n (𝒞 K) z →
      ∃ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
        (β : Subgroup G) (s : G), TwinYConfig p f (𝒞 K) K T z e J J' w e' β s

@[expose] def TwinYPatternAt (t : StatedLieTag) (n : ℕ)
    (Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 t n (𝒞 K) z →
      ∀ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
        (β : Subgroup G) (s : G), TwinYConfig p f (𝒞 K) K T z e J J' w e' β s →
        LocalOddCentral (𝒞 K) {e.u} → LocalOddCentral (𝒞 K) {e'.u} →
        LocalShapeT p f 0 (twinYModel (p ^ f) t n).1 (twinYModel (p ^ f) t n).2 (𝒞 K) e.u →
        LocalShapeT p f 0 (twinYModel (p ^ f) t n).1 (twinYModel (p ^ f) t n).2 (𝒞 K) e'.u →
        Pat (𝒞 K) K β s

@[expose] def TwinYPattern : Prop :=
  (∀ m, 4 ≤ m → TwinYPatternAt p f .POmegaPlus m (@PartnerPatternD p f m _)) ∧
    (∀ m, 4 ≤ m → TwinYPatternAt p f .POmegaMinus m
      (fun Ω K β t => PartnerPatternMinus p f m Ω K β t)) ∧
    (∀ m, 3 ≤ m → TwinYPatternAt p f .POmegaOdd m (@PartnerPatternBPair p f m _))

@[expose] def TwinYLinked : Prop :=
  (∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSp 2 (𝒞 K) z →
      ∀ (Λ : SpLayer p f 2 (𝒞 K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w →
          (∃ (T : Subgroup G) (e : TwinElt K T z), IsTwinAt (𝒞 K) K T z ∧
            IsClassicalMember p f T z ∧ LocalOddCentral (𝒞 K) {e.u} ∧
            LocalShapeT p f 0 (twinYModel (p ^ f) .PSp 2).1 (twinYModel (p ^ f) .PSp 2).2
              (𝒞 K) e.u) → LinkedAtProduct (𝒞 K) K z w) ∧
  (∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSU 4 (𝒞 K) z →
      ∀ (Λ : SuLayer p f 2 (𝒞 K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w →
          (∃ (T : Subgroup G) (e : TwinElt K T z), IsTwinAt (𝒞 K) K T z ∧
            IsClassicalMember p f T z ∧ LocalOddCentral (𝒞 K) {e.u} ∧
            LocalShapeT p f 0 (twinYModel (p ^ f) .PSU 4).1 (twinYModel (p ^ f) .PSU 4).2
              (𝒞 K) e.u) → LinkedAtProduct (𝒞 K) K z w)

structure TwinYInputs : Prop where
  p1 : TwinYP1 p f
  typ : TwinYType p f
  partner : TwinYPartner p f
  pattern : TwinYPattern p f

end Statements

section Assembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem localShapeT_at_member [Finite G] {K J : Subgroup G} {z w : G} (S : RouteDSetup p f K z)
    (hJ : J ∈ 𝒞 K) (hw : IsClassicalMember p f J w) {a : ℕ} {tY : StatedLieTag} {nY : ℕ}
    (h : LocalShapeT p f a tY nY (𝒞 K) z) : LocalShapeT p f a tY nY (𝒞 K) w := by
  obtain ⟨g, hg⟩ := hJ
  have hwg : w = g * z * g⁻¹ :=
    Gaps.unique_involution_of_isClassicalMember
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd)
      (S.exact J ⟨g, hg⟩) hw (hg ▸ S.cls.conj g)
  rw [hwg]
  exact h.conj S.inClass.conjInvariant g

theorem twinY_exists [Finite G] [IsSimpleGroup G] {t : StatedLieTag} {n : ℕ} (hrow : TwinRow t n)
    {Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop}
    (hY1 : TwinYP1 p f) (hY2 : TwinYType p f) (hY3 : TwinYPartner p f)
    (hY4 : TwinYPatternAt p f t n Pat) (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G}
    {z : G} (S : RouteDSetup p f K z) (hshape : LocalShapeT p f 2 t n (𝒞 K) z) :
    ∃ β ∈ 𝒞 K, ∃ s : G, IsClassicalMember p f β s ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ Pat (𝒞 K) K β s := by
  obtain ⟨T, e, J, J', w, e', β, s, hcfg⟩ := hY3 G hnab K z S t n hrow hshape
  have hP1 := hY1 G hnab K z S t n hrow hshape T hcfg.twin hcfg.clsT e
  have hty := hY2 G hnab K z S t n hrow hshape T hcfg.twin hcfg.clsT e hP1
  have hJΩ : J ∈ 𝒞 K := hcfg.mem_J.1
  have SJ : RouteDSetup p f J w := S.of_mem_conjClass hJΩ hcfg.clsJ
  have hcl : 𝒞 J = 𝒞 K := conjClass_eq_of_mem hJΩ
  have hshapeJ : LocalShapeT p f 2 t n (𝒞 J) w := by
    rw [hcl]
    exact localShapeT_at_member S hJΩ hcfg.clsJ hshape
  have htwinJ : IsTwinAt (𝒞 J) J J' w := by
    rw [hcl]
    exact hcfg.twinJ
  have hP1' := hY1 G hnab J w SJ t n hrow hshapeJ J' htwinJ hcfg.clsJ' e'
  have hty' := hY2 G hnab J w SJ t n hrow hshapeJ J' htwinJ hcfg.clsJ' e' hP1'
  rw [hcl] at hP1' hty'
  exact ⟨β, hcfg.memβ.1, s, hcfg.clsβ, hcfg.linear,
    hY4 G hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'⟩

theorem TwinYInputs.twinTDExists (h : TwinYInputs p f) :
    TwinTDExistsOn p f fun m => 4 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinY_exists (t := .POmegaMinus) (n := m)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))) h.p1 h.typ h.partner
    (h.pattern.2.1 m hm) hnab S hshape

theorem TwinYInputs.twinDExists (h : TwinYInputs p f) :
    TwinDExistsOn p f fun m => 4 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinY_exists (t := .POmegaPlus) (n := m) (Or.inl ⟨rfl, rfl, hm⟩) h.p1 h.typ h.partner
    (h.pattern.1 m hm) hnab S hshape

theorem TwinYInputs.twinBExists (h : TwinYInputs p f) :
    TwinBExistsOn p f fun m => 3 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape
  exact twinY_exists (t := .POmegaOdd) (n := m) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))) h.p1
    h.typ h.partner (h.pattern.2.2 m hm) hnab S hshape

theorem TwinYInputs.rows (hMFZ : Gaps.FundNoncentral p) (h : TwinYInputs p f) :
    RowPiece p f ShapeTwinD ∧ RowPiece p f ShapeTwinTD ∧ RowPiece p f ShapeTwinB :=
  ⟨rowTwinD_of_exists hMFZ h.twinDExists, rowTwinTD_of_exists hMFZ h.twinTDExists,
    rowTwinB_of_exists hMFZ h.twinBExists⟩

theorem TwinYInputs.twinSp2Linked (h : TwinYInputs p f) (hL : TwinYLinked p f) :
    TwinSp2Linked p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  obtain ⟨T, e, J, J', w', e', β, s, hcfg⟩ := h.partner G hnab K z S .PSp 2 hrow hshape
  have hP1 := h.p1 G hnab K z S .PSp 2 hrow hshape T hcfg.twin hcfg.clsT e
  have hty := h.typ G hnab K z S .PSp 2 hrow hshape T hcfg.twin hcfg.clsT e hP1
  exact hL.1 G hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw ⟨T, e, hcfg.twin, hcfg.clsT, hP1, hty⟩

theorem TwinYInputs.twinSU4Linked (h : TwinYInputs p f) (hL : TwinYLinked p f) :
    TwinSU4Linked p f := by
  intro G _ _ _ hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  obtain ⟨T, e, J, J', w', e', β, s, hcfg⟩ := h.partner G hnab K z S .PSU 4 hrow hshape
  have hP1 := h.p1 G hnab K z S .PSU 4 hrow hshape T hcfg.twin hcfg.clsT e
  have hty := h.typ G hnab K z S .PSU 4 hrow hshape T hcfg.twin hcfg.clsT e hP1
  exact hL.2 G hnab K z S hshape Λ K₂ hK₂ hK₂Λ w hw ⟨T, e, hcfg.twin, hcfg.clsT, hP1, hty⟩

end Assembly

end CFSG.ClassicalInvolution.RouteD.TwinY
