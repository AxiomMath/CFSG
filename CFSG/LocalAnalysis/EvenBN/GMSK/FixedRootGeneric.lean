module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRoot

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

abbrev StdType : Type 1 := ℕ → (S : Type) → [Group S] → Prop

@[expose] def StdType.IsoInvariant (T : StdType) : Prop :=
  ∀ (n : ℕ) (S S' : Type) [Group S] [Group S'], (S ≃* S') → T n S → T n S'

@[expose] def StdTypeFacts (T : StdType) : Prop :=
  ∀ (n : ℕ) (S : Type) [Group S] [Finite S], T n S →
    IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
      ∃ E : Subgroup S, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4

@[expose] def T_U3 : StdType := fun n S _ => 2 ≤ n ∧ LieModel S .PSU 3 2 n

@[expose] def T_Sz : StdType := fun n S _ => LieModel S .twistedB2 0 2 n

theorem StdType.lieModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ} (h : LieModel X t m p f) :
    LieModel Y t m p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isoInvariant_T_U3 : StdType.IsoInvariant T_U3 :=
  fun _ _ _ _ _ e h => ⟨h.1, StdType.lieModel_of_mulEquiv e h.2⟩

theorem isoInvariant_T_Sz : StdType.IsoInvariant T_Sz :=
  fun _ _ _ _ _ e h => StdType.lieModel_of_mulEquiv e h

structure FixedRootDatumOf (T : StdType) (D : Type) [Group D] (n : ℕ) (α : MulAut D)
    (S : Subgroup D) : Prop where
  orderOf_eq : orderOf α = 2
  le_fixed : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D)
  normal : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal
  type : T n S
  rankOne : FixedRootRankOne α S

@[expose] def FixedRootSelectorOf (T : StdType)
    (Surv : ℕ → (D : Type) → [Group D] → MulAut D → Prop)
    (P : (D : Type) → [Group D] → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → P D →
    ∀ (n : ℕ) (α : MulAut D) (S : Subgroup D), FixedRootDatumOf T D n α S → Surv n D α

@[expose] def SurvU3 (n : ℕ) (D : Type) [Group D] (α : MulAut D) : Prop :=
  LieModel D .PSL 3 2 (2 * n) ∧ α ∉ (MulAut.conj : D →* MulAut D).range

@[expose] def SurvSz (n : ℕ) (D : Type) [Group D] (α : MulAut D) : Prop :=
  LieModel D .PSp 2 2 n ∧ α ∉ (MulAut.conj : D →* MulAut D).range

theorem catalog_selectorOf {T : StdType}
    {Surv : ℕ → (D : Type) → [Group D] → MulAut D → Prop}
    (hT : ∀ (n : ℕ) (S : Type) [Group S] [Finite S], T n S → ∃ a b : S, a * b ≠ b * a)
    (hAlt : FixedRootSelectorOf T Surv fun D _ =>
      ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)))
    (hOdd : FixedRootSelectorOf T Surv fun D _ => OddLieType D)
    (hEven : FixedRootSelectorOf T Surv fun D _ => EvenLieType D)
    (hSpor : FixedRootSelectorOf T Surv fun D _ => NativeSporadic.SporadicRep D) :
    FixedRootSelectorOf T Surv fun D _ => Catalog D := by
  intro D _ _ hD hcat n α S d
  obtain ⟨a, b, hab⟩ := hT n S d.type
  have hnab : ∃ a b : D, a * b ≠ b * a := ⟨a, b, fun h => hab (Subtype.ext h)⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition D hnab).1 hcat with h | h | h | h
  · exact hAlt D hD h n α S d
  · exact hOdd D hD h n α S d
  · exact hEven D hD h n α S d
  · exact hSpor D hD h n α S d

section Normal

variable {G : Type} [Group G] {D : Subgroup G} [D.Normal] {t : G}

theorem fixedRootRankOne_conjNormal [Finite G] {A : Subgroup G} (hAD : A ≤ D)
    (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hrank : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) → IsPGroup 2 P → Nat.card P ≤ 2) :
    FixedRootRankOne (MulAut.conjNormal t : MulAut D) (A.subgroupOf D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP hP2
  set P' := P.map D.subtype with hP'
  have hP'A : P' ≤ centralizer (A : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h := mem_centralizer_iff.1 (hP hp).2 ⟨a, hAD ha⟩ (mem_subgroupOf.2 ha)
    exact congrArg Subtype.val h
  have hP't : P' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_centralizer_of_mem_eqLocus (hP hp).1
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hzN : P' ≤ normalizer (zpowers t : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
    intro p hp
    exact mem_centralizer_singleton_iff.1 (hP't hp)
  have hQ := IsPGroup.to_sup_of_normal_right' (hP2.map D.subtype) hz2 hzN
  have hQA : P' ⊔ zpowers t ≤ centralizer (A : Set G) := sup_le hP'A (zpowers_le.2 htA)
  have hQt : zpowers t = P' ⊔ zpowers t :=
    eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, ht]; exact hrank _ hQA hQ)
  have hP'le : P' ≤ zpowers t := hQt ▸ le_sup_left
  have hcard : Nat.card P = Nat.card P' := (card_map_of_injective D.subtype_injective).symm
  refine ⟨?_, fun hout => ?_⟩
  · rw [hcard]
    calc Nat.card P' ≤ Nat.card (zpowers t) := card_le_of_le hP'le
      _ = 2 := by rw [Nat.card_zpowers, ht]
  · by_contra hne
    obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hpt := hP'le ⟨p, hp, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hpt
    change t ^ k = (p : G) at hk
    have hpz : (p : G) = 1 ∨ (p : G) = t := by
      rw [← hk, ← zpow_mod_orderOf, ht]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [Nat.cast_ofNat, h, zpow_zero]
      · right
        rw [Nat.cast_ofNat, h, zpow_one]
    rcases hpz with h1 | htp
    · exact hp1 (Subtype.ext (Subtype.ext h1))
    · exact hout (conjNormal_mem_range_of_mem (htp ▸ p.2))

theorem fixedRootDatumOf_of_normal [Finite G] {T : StdType} {A : Subgroup G} (hAD : A ≤ D)
    (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hCt : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d)
    (hrank : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {n : ℕ} (hT : T n (A.subgroupOf D)) :
    FixedRootDatumOf T D n (MulAut.conjNormal t) (A.subgroupOf D) := by
  set F := (MulAut.conjNormal t : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D) with hF
  have hle : A.subgroupOf D ≤ F := fun s hs => by
    rw [hF, mem_eqLocus_conjNormal_iff]
    have hc := mem_centralizer_iff.1 htA s (mem_subgroupOf.1 hs)
    calc t * (s : G) * t⁻¹ = s * t * t⁻¹ := by rw [hc]
      _ = s := by group
  refine ⟨orderOf_conjNormal ht hnt, hle, ⟨fun x hx g => ?_⟩, hT,
    fixedRootRankOne_conjNormal hAD ht htA hrank⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
  have hgN := hCt (mem_centralizer_of_mem_eqLocus g.2)
  exact (mem_normalizer_iff.1 hgN _).1 hx

end Normal

theorem exists_fixedRootDatumOf_of_simple {T : StdType} (hiso : StdType.IsoInvariant T)
    {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G) {n : ℕ}
    {A : Subgroup G} (hA : T n A)
    (hrank : ∀ P : Subgroup G, P ≤ centralizer (A : Set G) → IsPGroup 2 P → Nat.card P ≤ 2)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hCt : centralizer ({t} : Set G) ≤ normalizer (A : Set G)) {D : Subgroup G} [D.Normal]
    (hAD : A ≤ D) (hD : IsSimpleGroup D) (hnt : ∃ d ∈ D, t⁻¹ * d * t ≠ d) :
    Catalog D ∧ ∃ S : Subgroup D, FixedRootDatumOf T D n (MulAut.conjNormal t) S :=
  ⟨CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hG D (MonoidHom.id D)
      Function.surjective_id,
    A.subgroupOf D, fixedRootDatumOf_of_normal hAD ht htA hCt hnt hrank
      (hiso n A (A.subgroupOf D) (subgroupOfEquivOfLe hAD).symm hA)⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
