module

public import CFSG.GH74.Generic.BProg.B1.PilotS5
public import CFSG.GH74.Generic.BProg.B1.PilotS3Models
public import CFSG.GH74.Generic.JMaxShapes

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.Open
open scoped commutatorElement

section Shape

theorem isSimpleGroup_of_qShape3 {Kt : Type} [Group Kt] (h : QShape3 Kt) : IsSimpleGroup Kt := by
  obtain ⟨p, f, -, -, -, hmod⟩ := h
  exact isSimpleGroup_of_lieModel_L3' hmod

theorem not_qShape1_of_center_trivial {Kt : Type} [Group Kt] (h1 : QShape1 Kt)
    (hZ : ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) : False := by
  have hc := IsSL4Model.natCard_center h1
  have hz : Subgroup.center Kt = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact hZ z (fun g => Subgroup.mem_center_iff.1 hz g)
  rw [hz, Subgroup.card_bot] at hc
  omega

theorem center_trivial_of_equiv {A X : Type} [Group A] [Group X] {Y : Subgroup X} (e : A ≃* ↥Y)
    (hA : ∀ z : A, (∀ g : A, g * z = z * g) → z = 1) :
    ∀ z ∈ Y, (∀ g ∈ Y, g * z = z * g) → z = 1 := by
  intro z hz hcomm
  have h1 : e.symm ⟨z, hz⟩ = 1 := by
    apply hA
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcomm _ (e g).2)
  have h2 : (⟨z, hz⟩ : ↥Y) = 1 := by
    have := congrArg e h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  exact congrArg Subtype.val h2

end Shape

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem center_trivial_of_shape3 {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1 :=
  center_trivial_of_simple_of_quasisimple (isSimpleGroup_of_qShape3 h3) (TwoThin.isQuasisimple_hat hK)

theorem exists_source_of_shape3 {x : G} {K : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ A : Subgroup G, IsSource2 x K A := by
  have hZ := center_trivial_of_shape3 hK h3
  exact exists_source_of_four hx hK hZ
    (exists_four_of_quasisimple_centerless (TwoThin.isQuasisimple_hat hK) hZ) (Or.inl h3)

theorem exists_adm_of_split3 {F : Type} [Field F] [Finite F] {x : G} {K A E : Subgroup G}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K)
    (hY : Split3Like F (imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hEnt : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE4]; norm_num)
  obtain ⟨⟨y, hyE⟩, hy1⟩ := exists_ne (1 : ↥E)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyK : y ∈ K := hEK hyE
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hy2sq : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) y hyE
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy2sq hy1'
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := fun h => hxK (h ▸ hyK)
  obtain ⟨hDcl, hDel, hD4⟩ := closure_pair_facts hx hy2 hxy hxyne
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  obtain ⟨hbmem, hbne, hb2⟩ := bar_facts hKC hyK hy2
  obtain ⟨L, hLY, hL, hrel⟩ := hY.exists_pair hbmem hb2
  have hyne : bar x y ∉ zpowers (xbar x) := bar_not_mem_zpowers_xbar hx hK hxK hyK hy2
  have hDA : D ≤ A := by
    rw [hD, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h, hAE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · rw [Set.mem_singleton_iff.1 h, hAE]; exact Subgroup.mem_sup_left hyE
  have hDC : D ≤ centralizer ({x} : Set G) := by
    rw [hD, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · rw [Set.mem_singleton_iff.1 h]; exact hyC
  have hDrank : 2 ≤ pRank 2 ↥D := by
    have := CFSG.pRank_eq_of_card_eq_pow (A := ↥D) Nat.one_lt_two (k := 2) (by rw [hD4]; norm_num)
    omega
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hLD : L ≤ centralizer ((imgBar x D : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) := by
    set Q : Subgroup G := ((centralizer (L : Set (CentralizerBar x))).comap (proj x)).map
      (centralizer ({x} : Set G)).subtype with hQ
    have hxQ : x ∈ Q := ⟨⟨x, hxC⟩, by
      show proj x ⟨x, hxC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      exact Subgroup.mem_centralizer_iff.2 fun l _ =>
        (Subgroup.mem_center_iff.1 (xbar_mem_center x)) l, rfl⟩
    have hyQ : y ∈ Q := ⟨⟨y, hyC⟩, by
      show proj x ⟨y, hyC⟩ ∈ centralizer (L : Set (CentralizerBar x))
      rw [← bar_of_mem hyC]
      exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.1 (hL.le_H hl).1, rfl⟩
    have hDQ : D ≤ Q := by
      rw [hD, Subgroup.closure_le]
      intro a ha
      rcases ha with h | h
      · rw [h]; exact hxQ
      · rw [Set.mem_singleton_iff.1 h]; exact hyQ
    intro l hl
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨c', hc', rfl⟩ := hg
    obtain ⟨c'', hc'', hcc⟩ := hDQ hc'
    have : c'' = c' := Subtype.ext hcc
    subst this
    exact (Subgroup.mem_centralizer_iff.1 hc'' l hl).symm
  have hLself : pLayerOf 2 (centralizer ((imgBar x D : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) ⊓ L) = L := by
    rw [inf_eq_right.2 hLD]
    exact le_antisymm (sSup_le fun L' hL' => hL'.1) (le_sSup hL.isPCompIn_self)
  have hDcomm : D ≤ centralizer (D : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb =>
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥D)).comm ⟨b, hb⟩ ⟨a, ha⟩)
  refine ⟨y, L, ⟨⟨hyC, hy2, hyne, hrel, fun _ => ⟨hL.isPCompIn, fun L' hL' _ =>
    hL.card_le_of_isPCompIn hL'⟩⟩, D, L, ⟨hDA, hDel, hDrank⟩,
    Or.inl ⟨⟨hyC, hy2, hyne, hDC, hDel, fun d hd => Subgroup.le_normalizer hd, ?_⟩,
      Subgroup.le_normalizer hyK, hL.pLayerOf_ne_bot, hL.isPCompIn, ?_⟩⟩⟩
  · rw [inf_eq_left.2 hDcomm]
    exact hDrank
  · rw [hLself]; exact hL.isPCompIn_self

theorem exists_adm_of_shape3 {x : G} {K A : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hA : IsSource2 x K A) :
    ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb := by
  obtain ⟨-, -, -, hcase⟩ := hA
  have hZ := center_trivial_of_shape3 hK h3
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, -⟩
  · exact (not_qShape1_of_center_trivial h1 hZ).elim
  · have hxK : x ∉ K := not_mem_of_center_trivial hx hK.1 hZ
    obtain ⟨eK⟩ := hat_equiv_imgBar hK
    obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := exists_equiv_grpS3_of_qShape3 h3
    have hY : Split3Like F (imgBar x K) :=
      Split3Like.of_equiv (eK.symm.trans e) hP (center_trivial_of_equiv eK hZ)
    exact exists_adm_of_split3 hx hK hxK hY hEK hAE hEel hE4

end GLevel

end CFSG.GH74.Generic.BProg.B1.PilotS3

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem sourceExistsFor_shape3 : SourceExistsFor QShape3 := by
  intro G _ _ _hyp _noAlt x K hcirc h3
  exact PilotS3.exists_source_of_shape3 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h3

theorem admissibleExistsFor_shape3 : AdmissibleExistsFor QShape3 := by
  intro G _ _ _hyp _noAlt x K hcirc h3 A hA
  exact PilotS3.exists_adm_of_shape3 hcirc.1.1.1.1 hcirc.1.1.1.2.2 h3 hA

end CFSG.GH74.Generic.BProg.B1
