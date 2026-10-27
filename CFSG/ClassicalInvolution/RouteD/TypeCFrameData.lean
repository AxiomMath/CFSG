module

public import CFSG.ClassicalInvolution.RouteD.TypeCLocal
public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.QuaternionStructure
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv)
open CFSG.ClassicalInvolution.WeakCT (diagTorus2)
open scoped MatrixGroups commutatorElement

structure CSetup (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  three : 3 ≤ m
  inClass : InClass p f Ω
  exact : ExactMembers Ω
  mem : K ∈ Ω
  cls : IsClassicalMember p f K z
  single : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K
  centerTriv : Subgroup.center G = ⊥
  shape : LocalShapeC p f m Ω z
  p1cl : ∀ L ∈ Ω, ∀ y : G, IsClassicalMember p f L y → LocalOddCentral Ω {y}
  ih : LocalLieSystems p f Ω

@[expose] def AllLocalOddCentral {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ x : G, orderOf x = 2 → LocalOddCentral Ω {x}

@[expose] def NoOtherComponents (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) : Prop :=
  ∀ x : G, orderOf x = 2 → ∀ (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (c : Fin D.card), (D.tag c = .PSL ∧ D.rank c = 2) ∨ D.tag c = .PSp

structure CSetupAll (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) : Prop extends CSetup p f m Ω K z where
  p1 : AllLocalOddCentral Ω
  noOther : NoOtherComponents p f Ω

section Setup

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

theorem CSetup.two_le (S : CSetup p f m Ω K z) : 2 ≤ m := by
  have := S.three
  omega

theorem CSetup.z_ne_one (S : CSetup p f m Ω K z) : z ≠ 1 := by
  intro h
  have := S.cls.orderOf_eq_two
  rw [h, orderOf_one] at this
  omega

theorem CSetup.conjInvariant (S : CSetup p f m Ω K z) : ConjInvariant Ω :=
  S.inClass.conjInvariant

theorem CSetup.card_eq (S : CSetup p f m Ω K z) : Nat.card (GaloisField p f) = p ^ f :=
  natCard_galoisField_of_five_le S.five

theorem CSetup.four_le (S : CSetup p f m Ω K z) : 4 ≤ Nat.card (GaloisField p f) :=
  four_le_natCard_galoisField S.five

theorem CSetup.odd_card (S : CSetup p f m Ω K z) : Odd (Nat.card (GaloisField p f)) := by
  rw [S.card_eq]
  exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow

theorem CSetup.two_ne_zero (S : CSetup p f m Ω K z) : (2 : GaloisField p f) ≠ 0 :=
  CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard S.odd_card

theorem CSetup.hex (S : CSetup p f m Ω K z) :
    ∃ a : (GaloisField p f)ˣ, (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : _) :=
  exists_unit_ne_inv S.five

theorem CSetup.p1_z (S : CSetup p f m Ω K z) : LocalOddCentral Ω {z} :=
  S.p1cl K S.mem z S.cls

theorem CSetup.exists_lieSystemData (S : CSetup p f m Ω K z) {x : G} (hx : orderOf x = 2) :
    Nonempty (LieSystemData p f (locQuot Ω x) (locFamily Ω x)) := by
  refine S.ih {x} ?_
  intro h
  have : x ∈ Subgroup.center G := h (Set.mem_singleton x)
  rw [S.centerTriv, Subgroup.mem_bot] at this
  subst this
  simp at hx

end Setup

structure Frame (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  Kf : Fin (m + 1) → Subgroup G
  gf : Fin (m + 1) → G
  ι : Fin (m + 1) → (SL(2, GaloisField p f) →* G)
  mem : ∀ i, Kf i ∈ Ω
  eq_conj : ∀ i, Kf i = conjSub (gf i) K
  commute : ∀ i j, i ≠ j → Commutes (Kf i) (Kf j)
  ι_inj : ∀ i, Function.Injective (ι i)
  range_ι : ∀ i, (ι i).range = Kf i

section FrameAPI

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G} (Fr : Frame p f m Ω K z)

namespace Frame

@[expose] def zf (i : Fin (m + 1)) : G := Fr.gf i * z * (Fr.gf i)⁻¹

@[expose] noncomputable def Tf (i : Fin (m + 1)) : Subgroup G :=
  (diagTorus2 (GaloisField p f)).map (Fr.ι i)

variable {Fr}

theorem cls (S : CSetup p f m Ω K z) (i : Fin (m + 1)) :
    IsClassicalMember p f (Fr.Kf i) (Fr.zf i) := by
  rw [Fr.eq_conj i]
  exact S.cls.conj (Fr.gf i)

theorem zf_mem (S : CSetup p f m Ω K z) (i : Fin (m + 1)) : Fr.zf i ∈ Fr.Kf i :=
  (Fr.cls S i).mem

theorem Tf_le (i : Fin (m + 1)) : Fr.Tf i ≤ Fr.Kf i := by
  rintro _ ⟨a, -, rfl⟩
  rw [← Fr.range_ι i]
  exact ⟨a, rfl⟩

theorem ne_of_ne (S : CSetup p f m Ω K z) {i j : Fin (m + 1)} (hij : i ≠ j) :
    Fr.Kf i ≠ Fr.Kf j := by
  intro h
  have hc := Fr.commute i j hij
  rw [← h] at hc
  exact not_commutes_self_of_isClassicalMember (Fr.cls S i) hc

theorem injective_Kf (S : CSetup p f m Ω K z) : Function.Injective Fr.Kf :=
  fun _ _ h => by_contra fun hij => Fr.ne_of_ne S hij h

theorem commute_zf (S : CSetup p f m Ω K z) (i j : Fin (m + 1)) :
    ∀ y ∈ Fr.Kf i, y * Fr.zf j = Fr.zf j * y := by
  intro y hy
  by_cases hij : i = j
  · subst hij
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_isClassicalMember (Fr.cls S i) hy)
  · exact Fr.commute i j hij y hy _ (Fr.zf_mem S j)

theorem zf_comm (S : CSetup p f m Ω K z) (i j : Fin (m + 1)) :
    Fr.zf i * Fr.zf j = Fr.zf j * Fr.zf i :=
  Fr.commute_zf S i j _ (Fr.zf_mem S i)

theorem ι_neg_one (S : CSetup p f m Ω K z) (i : Fin (m + 1)) : Fr.ι i (-1) = Fr.zf i := by
  have hz := Fr.zf_mem S i
  rw [← Fr.range_ι i] at hz
  obtain ⟨A, hA⟩ := hz
  have hcen : A ∈ Subgroup.center SL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply Fr.ι_inj i
    rw [map_mul, map_mul, hA]
    exact Fr.commute_zf S i i (Fr.ι i B) (by rw [← Fr.range_ι i]; exact ⟨B, rfl⟩)
  rcases mem_center_specialLinearGroup_two_iff.mp hcen with h | h
  · exfalso
    have h1 : Fr.zf i = 1 := by rw [← hA, h, map_one]
    have := (Fr.cls S i).orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  · rw [← hA, h]

end Frame

end FrameAPI

section Existence

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem commutes_map_planeGroup_std {F : Type} [Field F] {X : Type*} [Group X]
    (ψ : StatedSp m F →* X) {k l : Fin m} (hkl : k ≠ l) :
    Commutes ((planeGroup (stdPlane F m k)).map ψ) ((planeGroup (stdPlane F m l)).map ψ) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  rw [Models.SymplecticPairs.planeGroup_stdPlane] at ha hb
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  exact (Models.SymplecticPairs.commute_longBlock_longBlock hkl A B).eq

theorem exists_frame (S : CSetup p f m Ω K z) : Nonempty (Frame p f m Ω K z) := by
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass S.mem S.cls S.shape
  have hP := S.p1_z
  choose L hLcent hLK hLimg using fun k : Fin m => typeC_exists_member_of_plane S.two_le S.five
    S.inClass S.mem S.cls hP d (isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := m) k)
  let Kf : Fin (m + 1) → Subgroup G := Fin.cons K L
  have hKf0 : Kf 0 = K := Fin.cons_zero _ _
  have hKfs : ∀ k : Fin m, Kf k.succ = L k := fun k => Fin.cons_succ _ _ _
  have hmem : ∀ i, Kf i ∈ Ω := by
    intro i
    induction i using Fin.cases with
    | zero => rw [hKf0]; exact S.mem
    | succ k => rw [hKfs]; exact (hLcent k).1
  have hcomm : ∀ i j, i ≠ j → Commutes (Kf i) (Kf j) := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ l =>
        rw [hKf0, hKfs]
        exact typeC_commutes_K_of_ne S.two_le S.five S.inClass S.exact S.mem S.cls hP d
          (hLcent l) (hLK l)
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [hKf0, hKfs]
        exact (typeC_commutes_K_of_ne S.two_le S.five S.inClass S.exact S.mem S.cls hP d
          (hLcent k) (hLK k)).symm
      | succ l =>
        have hkl : k ≠ l := fun h => hij (by rw [h])
        rw [hKfs, hKfs]
        exact commutes_of_commutes_locImg S.inClass hP (hLcent k) (hLcent l)
          (by rw [hLimg k, hLimg l]; exact commutes_map_planeGroup_std d.ψ hkl)
  choose g hg using fun i => S.single (Kf i) (hmem i)
  have hcls : ∀ i, IsClassicalMember p f (Kf i) (g i * z * (g i)⁻¹) := by
    intro i
    rw [hg i]
    exact S.cls.conj (g i)
  have hequiv : ∀ i, Nonempty (↥(Kf i) ≃* SL(2, GaloisField p f)) := fun i =>
    (hcls i).nonempty_equiv_sl2 (S.exact _ (hmem i))
  let e : ∀ i, ↥(Kf i) ≃* SL(2, GaloisField p f) := fun i => (hequiv i).some
  refine ⟨{ Kf := Kf, gf := g, ι := fun i => (Kf i).subtype.comp (e i).symm.toMonoidHom,
            mem := hmem, eq_conj := hg, commute := hcomm, ι_inj := ?_, range_ι := ?_ }⟩
  · intro i
    exact (Kf i).subtype_injective.comp (e i).symm.injective
  · intro i
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ((e i).symm A).2
    · intro hx
      exact ⟨e i ⟨x, hx⟩, by simp⟩

end Existence

section Reparam

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

@[expose] noncomputable def ShapeCDict.reparam (d : ShapeCDict p f m Ω z) (hm : 1 ≤ m)
    (g : StatedSp m (GaloisField p f)) : ShapeCDict p f m Ω z where
  ψ := d.ψ.comp (MulAut.conj g).toMonoidHom
  ker_le := by
    intro x hx
    refine Models.SymplecticPairs.mem_center_of_conj_mem_center (g := g) ?_
    have hx' : d.ψ (g * x * g⁻¹) = 1 := MonoidHom.mem_ker.mp hx
    exact d.ker_le (MonoidHom.mem_ker.mpr hx')
  Q₀ := d.Q₀
  commutes := by
    have h : (d.ψ.comp (MulAut.conj g).toMonoidHom).range = d.ψ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective,
        ← MonoidHom.range_eq_map]
    rw [h]
    exact d.commutes
  mem_fam := by
    intro P hP
    obtain ⟨P', hP', h⟩ := exists_planeGroup_conj hm hP g
    have : (planeGroup P).map (d.ψ.comp (MulAut.conj g).toMonoidHom) =
        (planeGroup P').map d.ψ := by
      rw [← Subgroup.map_map, h]
    rw [this]
    exact d.mem_fam P' hP'
  fam_cases := by
    intro K' hK'
    rcases d.fam_cases K' hK' with h | ⟨P, hP, hK⟩
    · exact Or.inl h
    · obtain ⟨P'', hP'', h''⟩ := exists_planeGroup_conj hm hP g⁻¹
      refine Or.inr ⟨P'', hP'', ?_⟩
      have hcc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id _ := by
        ext y
        simp [mul_assoc]
      rw [hK, ← Subgroup.map_map]
      have : (planeGroup P'').map (MulAut.conj g).toMonoidHom = planeGroup P := by
        rw [← h'', Subgroup.map_map, hcc, Subgroup.map_id]
      rw [this]
  card_le := d.card_le

end Reparam

section LocHom

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def locHom (Ω : Set (Subgroup G)) (x : G) {H : Type*} [Group H]
    (θ : H →* G) (h : ∀ a, θ a ∈ locLayer Ω x) : H →* locQuot Ω x :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).comp
    (θ.codRestrict (locLayer Ω x) h)

theorem locHom_apply {x : G} {H : Type*} [Group H] (θ : H →* G) (h : ∀ a, θ a ∈ locLayer Ω x)
    (a : H) : locHom Ω x θ h a = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
      ⟨θ a, h a⟩ := rfl

theorem map_locHom {x : G} {H : Type*} [Group H] (θ : H →* G) (h : ∀ a, θ a ∈ locLayer Ω x)
    (A : Subgroup H) : A.map (locHom Ω x θ h) = locImg Ω x (A.map θ) := by
  unfold locHom locImg
  rw [← Subgroup.map_map, Models.SymplecticPairs.map_codRestrict_eq]

theorem range_locHom {x : G} {H : Type*} [Group H] (θ : H →* G) (h : ∀ a, θ a ∈ locLayer Ω x) :
    (locHom Ω x θ h).range = locImg Ω x θ.range := by
  rw [MonoidHom.range_eq_map, map_locHom, ← MonoidHom.range_eq_map]

theorem subgroupOf_inf_oddCore_eq_bot [Finite G] (hex : ExactMembers Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) :
    L.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥ := by
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  exact inf_oddCore_eq_bot hO

theorem locHom_injective [Finite G] (hex : ExactMembers Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {H : Type*} [Group H] {θ : H →* G}
    (hθ : Function.Injective θ) (hr : θ.range ≤ L) (h : ∀ a, θ a ∈ locLayer Ω x) :
    Function.Injective (locHom Ω x θ h) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (⟨θ a, h a⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have h2 : (⟨θ a, h a⟩ : ↥(locLayer Ω x)) ∈ L.subgroupOf (locLayer Ω x) :=
    Subgroup.mem_subgroupOf.mpr (hr ⟨a, rfl⟩)
  have h3 := subgroupOf_inf_oddCore_eq_bot hex hL
  have h4 : (⟨θ a, h a⟩ : ↥(locLayer Ω x)) ∈
      L.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) := ⟨h2, h1⟩
  rw [h3, Subgroup.mem_bot] at h4
  apply hθ
  rw [map_one]
  exact congrArg Subtype.val h4

end LocHom

section LocalFrame

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

theorem Frame.mem_cent (Fr : Frame p f m Ω K z) (S : CSetup p f m Ω K z) (i l : Fin (m + 1)) :
    Fr.Kf i ∈ centralizingMembers Ω {Fr.zf l} :=
  ⟨Fr.mem i, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (Fr.commute_zf S i l y hy)⟩

theorem Frame.Kf_le_locLayer (Fr : Frame p f m Ω K z) (S : CSetup p f m Ω K z) (i l : Fin (m + 1)) :
    Fr.Kf i ≤ locLayer Ω (Fr.zf l) :=
  le_centralizingLayer (Fr.mem_cent S i l)

structure LocalFrame (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) where
  d : ShapeCDict p f m Ω (Fr.zf l)
  adapted : ∀ k : Fin m, (longBlock (GaloisField p f) m k).range.map d.ψ =
    locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k))
  torus : ∀ k : Fin m, (planeTorus (GaloisField p f) m k).map d.ψ =
    locImg Ω (Fr.zf l) (Fr.Tf (l.succAbove k))

variable [Finite G]

theorem exists_localFrame (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) :
    Nonempty (LocalFrame Fr l) := by
  have hPl : LocalOddCentral Ω {Fr.zf l} := S.p1cl _ (Fr.mem l) _ (Fr.cls S l)
  obtain ⟨d₀⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem l) (Fr.cls S l)
    (S.shape.conj S.conjInvariant (Fr.gf l))
  have hne : ∀ k : Fin m, Fr.Kf (l.succAbove k) ≠ Fr.Kf l := fun k =>
    Fr.ne_of_ne S (Fin.succAbove_ne l k)
  have hR : ∀ k : Fin m, ∃ P, IsHyperbolicPlane P ∧
      locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) = (planeGroup P).map d₀.ψ := fun k =>
    typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem l) (Fr.cls S l) hPl d₀
      (Fr.mem_cent S _ l) (hne k)
  have hinj : Function.Injective fun k : Fin m => locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) := by
    intro k k' h
    have := locImg_injOn S.inClass hPl (Fr.mem_cent S _ l) (Fr.mem_cent S _ l) h
    exact Fin.succAbove_right_injective (Fr.injective_Kf S this)
  have hcomm : ∀ k k' : Fin m, k ≠ k' → ∀ x ∈ locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)),
      ∀ y ∈ locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k')), x * y = y * x := fun k k' hkk' =>
    commutes_locImg_of_commutes (Fr.commute _ _
      (fun h => hkk' (Fin.succAbove_right_injective h)))
  have hT : ∀ k : Fin m, ∃ β : SL(2, GaloisField p f) →* locQuot Ω (Fr.zf l),
      Function.Injective β ∧ β.range = locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) ∧
        (diagTorus2 (GaloisField p f)).map β = locImg Ω (Fr.zf l) (Fr.Tf (l.succAbove k)) := by
    intro k
    have hle : ∀ a, Fr.ι (l.succAbove k) a ∈ locLayer Ω (Fr.zf l) := fun a =>
      Fr.Kf_le_locLayer S _ l (by rw [← Fr.range_ι]; exact ⟨a, rfl⟩)
    refine ⟨locHom Ω (Fr.zf l) (Fr.ι (l.succAbove k)) hle, ?_, ?_, ?_⟩
    · exact locHom_injective S.exact (Fr.mem_cent S _ l) (Fr.ι_inj _)
        (by rw [Fr.range_ι]) hle
    · rw [range_locHom, Fr.range_ι]
    · rw [map_locHom]
      rfl
  obtain ⟨g, hg1, hg2⟩ := Models.SymplecticPairs.exists_adapted_model (by have := S.two_le; omega)
    S.two_ne_zero S.hex d₀.ψ d₀.ker_le (fun k => locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k))) hR
    hinj hcomm (fun k => locImg Ω (Fr.zf l) (Fr.Tf (l.succAbove k))) hT
  exact ⟨{ d := d₀.reparam (by have := S.two_le; omega) g, adapted := hg1, torus := hg2 }⟩

end LocalFrame

end CFSG.ClassicalInvolution.RouteD
