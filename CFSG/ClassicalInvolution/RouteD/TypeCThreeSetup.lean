module

public import CFSG.ClassicalInvolution.RouteD.TypeCFrameData

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.QuaternionStructure
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv)
open CFSG.ClassicalInvolution.WeakCT (diagTorus2)
open scoped MatrixGroups commutatorElement

structure CSetupW (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  two : 2 ≤ m
  inClass : InClass p f Ω
  exact : ExactMembers Ω
  mem : K ∈ Ω
  cls : IsClassicalMember p f K z
  single : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K
  shape : LocalShapeC p f m Ω z
  p1cl : ∀ L ∈ Ω, ∀ y : G, IsClassicalMember p f L y → LocalOddCentral Ω {y}

section Setup

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

theorem CSetupW.two_le (S : CSetupW p f m Ω K z) : 2 ≤ m := S.two

theorem CSetupW.conjInvariant (S : CSetupW p f m Ω K z) : ConjInvariant Ω :=
  S.inClass.conjInvariant

theorem CSetupW.card_eq (S : CSetupW p f m Ω K z) : Nat.card (GaloisField p f) = p ^ f :=
  natCard_galoisField_of_five_le S.five

theorem CSetupW.four_le (S : CSetupW p f m Ω K z) : 4 ≤ Nat.card (GaloisField p f) :=
  four_le_natCard_galoisField S.five

theorem CSetupW.odd_card (S : CSetupW p f m Ω K z) : Odd (Nat.card (GaloisField p f)) := by
  rw [S.card_eq]
  exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow

theorem CSetupW.two_ne_zero (S : CSetupW p f m Ω K z) : (2 : GaloisField p f) ≠ 0 :=
  CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard S.odd_card

theorem CSetupW.hex (S : CSetupW p f m Ω K z) :
    ∃ a : (GaloisField p f)ˣ, (a : GaloisField p f) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : _) :=
  exists_unit_ne_inv S.five

theorem CSetupW.p1_z (S : CSetupW p f m Ω K z) : LocalOddCentral Ω {z} :=
  S.p1cl K S.mem z S.cls

end Setup

namespace Frame

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G} {Fr : Frame p f m Ω K z}

theorem clsW (S : CSetupW p f m Ω K z) (i : Fin (m + 1)) :
    IsClassicalMember p f (Fr.Kf i) (Fr.zf i) := by
  rw [Fr.eq_conj i]
  exact S.cls.conj (Fr.gf i)

theorem zf_memW (S : CSetupW p f m Ω K z) (i : Fin (m + 1)) : Fr.zf i ∈ Fr.Kf i :=
  (Fr.clsW S i).mem

theorem ne_of_neW (S : CSetupW p f m Ω K z) {i j : Fin (m + 1)} (hij : i ≠ j) :
    Fr.Kf i ≠ Fr.Kf j := by
  intro h
  have hc := Fr.commute i j hij
  rw [← h] at hc
  exact not_commutes_self_of_isClassicalMember (Fr.clsW S i) hc

theorem injective_KfW (S : CSetupW p f m Ω K z) : Function.Injective Fr.Kf :=
  fun _ _ h => by_contra fun hij => Fr.ne_of_neW S hij h

theorem commute_zfW (S : CSetupW p f m Ω K z) (i j : Fin (m + 1)) :
    ∀ y ∈ Fr.Kf i, y * Fr.zf j = Fr.zf j * y := by
  intro y hy
  by_cases hij : i = j
  · subst hij
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_isClassicalMember (Fr.clsW S i) hy)
  · exact Fr.commute i j hij y hy _ (Fr.zf_memW S j)

theorem zf_commW (S : CSetupW p f m Ω K z) (i j : Fin (m + 1)) :
    Fr.zf i * Fr.zf j = Fr.zf j * Fr.zf i :=
  Fr.commute_zfW S i j _ (Fr.zf_memW S i)

theorem ι_neg_oneW (S : CSetupW p f m Ω K z) (i : Fin (m + 1)) : Fr.ι i (-1) = Fr.zf i := by
  have hz := Fr.zf_memW S i
  rw [← Fr.range_ι i] at hz
  obtain ⟨A, hA⟩ := hz
  have hcen : A ∈ Subgroup.center SL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply Fr.ι_inj i
    rw [map_mul, map_mul, hA]
    exact Fr.commute_zfW S i i (Fr.ι i B) (by rw [← Fr.range_ι i]; exact ⟨B, rfl⟩)
  rcases mem_center_specialLinearGroup_two_iff.mp hcen with h | h
  · exfalso
    have h1 : Fr.zf i = 1 := by rw [← hA, h, map_one]
    have := (Fr.clsW S i).orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  · rw [← hA, h]

end Frame

section Existence

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_frameW (S : CSetupW p f m Ω K z) : Nonempty (Frame p f m Ω K z) := by
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

section LocalFrames

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

theorem Frame.mem_centW (Fr : Frame p f m Ω K z) (S : CSetupW p f m Ω K z) (i l : Fin (m + 1)) :
    Fr.Kf i ∈ centralizingMembers Ω {Fr.zf l} :=
  ⟨Fr.mem i, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (Fr.commute_zfW S i l y hy)⟩

theorem Frame.Kf_le_locLayerW (Fr : Frame p f m Ω K z) (S : CSetupW p f m Ω K z)
    (i l : Fin (m + 1)) : Fr.Kf i ≤ locLayer Ω (Fr.zf l) :=
  le_centralizingLayer (Fr.mem_centW S i l)

theorem Frame.p1W (S : CSetupW p f m Ω K z) (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) :
    LocalOddCentral Ω {Fr.zf l} :=
  S.p1cl _ (Fr.mem l) _ (Fr.clsW S l)

variable [Finite G]

theorem exists_localFrameW (S : CSetupW p f m Ω K z) (Fr : Frame p f m Ω K z) (l : Fin (m + 1)) :
    Nonempty (LocalFrame Fr l) := by
  have hPl : LocalOddCentral Ω {Fr.zf l} := Fr.p1W S l
  obtain ⟨d₀⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem l) (Fr.clsW S l)
    (S.shape.conj S.conjInvariant (Fr.gf l))
  have hne : ∀ k : Fin m, Fr.Kf (l.succAbove k) ≠ Fr.Kf l := fun k =>
    Fr.ne_of_neW S (Fin.succAbove_ne l k)
  have hR : ∀ k : Fin m, ∃ P, IsHyperbolicPlane P ∧
      locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) = (planeGroup P).map d₀.ψ := fun k =>
    typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem l) (Fr.clsW S l) hPl d₀
      (Fr.mem_centW S _ l) (hne k)
  have hinj : Function.Injective fun k : Fin m => locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) := by
    intro k k' h
    have := locImg_injOn S.inClass hPl (Fr.mem_centW S _ l) (Fr.mem_centW S _ l) h
    exact Fin.succAbove_right_injective (Fr.injective_KfW S this)
  have hcomm : ∀ k k' : Fin m, k ≠ k' → ∀ x ∈ locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)),
      ∀ y ∈ locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k')), x * y = y * x := fun k k' hkk' =>
    commutes_locImg_of_commutes (Fr.commute _ _
      (fun h => hkk' (Fin.succAbove_right_injective h)))
  have hT : ∀ k : Fin m, ∃ β : SL(2, GaloisField p f) →* locQuot Ω (Fr.zf l),
      Function.Injective β ∧ β.range = locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k)) ∧
        (diagTorus2 (GaloisField p f)).map β = locImg Ω (Fr.zf l) (Fr.Tf (l.succAbove k)) := by
    intro k
    have hle : ∀ a, Fr.ι (l.succAbove k) a ∈ locLayer Ω (Fr.zf l) := fun a =>
      Fr.Kf_le_locLayerW S _ l (by rw [← Fr.range_ι]; exact ⟨a, rfl⟩)
    refine ⟨locHom Ω (Fr.zf l) (Fr.ι (l.succAbove k)) hle, ?_, ?_, ?_⟩
    · exact locHom_injective S.exact (Fr.mem_centW S _ l) (Fr.ι_inj _)
        (by rw [Fr.range_ι]) hle
    · rw [range_locHom, Fr.range_ι]
    · rw [map_locHom]
      rfl
  obtain ⟨g, hg1, hg2⟩ := Models.SymplecticPairs.exists_adapted_model (by have := S.two_le; omega)
    S.two_ne_zero S.hex d₀.ψ d₀.ker_le (fun k => locImg Ω (Fr.zf l) (Fr.Kf (l.succAbove k))) hR
    hinj hcomm (fun k => locImg Ω (Fr.zf l) (Fr.Tf (l.succAbove k))) hT
  exact ⟨{ d := d₀.reparam (by have := S.two_le; omega) g, adapted := hg1, torus := hg2 }⟩

end LocalFrames

end CFSG.ClassicalInvolution.RouteD
