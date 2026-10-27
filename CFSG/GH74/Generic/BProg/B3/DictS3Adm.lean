module

public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts
public import CFSG.GH74.Generic.BProg.B1.PilotS5

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSource2_of_four {x : G} {Iw E : Subgroup G} (hx : orderOf x = 2)
    (hIw : IsPCompIn 2 (centralizer ({x} : Set G)) Iw) (hxIw : x ∉ Iw)
    (h3 : QShape3 (↥Iw ⧸ pPrimeCore 2 ↥Iw)) (hEIw : E ≤ Iw) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hE4 : Nat.card ↥E = 4) : IsSource2 x Iw (E ⊔ zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : Iw ≤ centralizer ({x} : Set G) := hIw.1
  have hxE : x ∉ E := fun h => hxIw (hEIw h)
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hzE : zpowers x ≤ centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hKC (hEIw he)))
  refine ⟨?_, ?_, ?_, Or.inr ⟨E, hEIw, rfl, hxE, hEel, hE4, Or.inl h3⟩⟩
  · exact sup_le (hEIw.trans hKC) (Subgroup.zpowers_le.2 hxC)
  · exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hzE
  · have hnorm : zpowers x ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (hzE ha)
    have hdisj : Disjoint E (zpowers x) := by
      rw [Subgroup.disjoint_def]
      intro a haE hax
      rcases mem_zpowers_of_two hx hax with h | h
      · exact h
      · exact absurd (h ▸ haE) hxE
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers x) hnorm hdisj,
      Nat.card_zpowers, hx, hE4]

theorem isAdmPair_of_split3_at {F : Type} [Field F] [Finite F] {x y : G} {K A E : Subgroup G}
    {L : Subgroup (CentralizerBar x)} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxK : x ∉ K)
    (hY : B1.PilotS3.Split3Like F (S3.imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (_hE4 : Nat.card ↥E = 4) (hyE : y ∈ E) (hy1 : y ≠ 1)
    (hLY : L ≤ S3.imgBar x K)
    (hL : B1.PilotS3.IsSplit3 F (bar x y) L
      (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S3.imgBar x K)) :
    IsAdmPair x K A y L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hyK : y ∈ K := hEK hyE
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have hy2sq : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) y hyE
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy2sq hy1
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm
  have hxyne : x ≠ y := fun h => hxK (h ▸ hyK)
  obtain ⟨hDcl, hDel, hD4⟩ := closure_pair_facts hx hy2 hxy hxyne
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  obtain ⟨hbmem, hbne, hb2⟩ := bar_facts hKC hyK hy2
  have hrel := hY.subtermRel hbmem hLY hL
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
  have hLD : L ≤ centralizer ((S3.imgBar x D : Subgroup (CentralizerBar x)) :
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
  have hLself : pLayerOf 2 (centralizer ((S3.imgBar x D : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)) ⊓ L) = L := by
    rw [inf_eq_right.2 hLD]
    exact le_antisymm (sSup_le fun L' hL' => hL'.1) (le_sSup hL.isPCompIn_self)
  have hDcomm : D ≤ centralizer (D : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb =>
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥D)).comm ⟨b, hb⟩ ⟨a, ha⟩)
  refine ⟨⟨hyC, hy2, hyne, hrel, fun _ => ⟨hL.isPCompIn, fun L' hL' _ =>
    hL.card_le_of_isPCompIn hL'⟩⟩, D, L, ⟨hDA, hDel, hDrank⟩,
    Or.inl ⟨⟨hyC, hy2, hyne, hDC, hDel, fun d hd => Subgroup.le_normalizer hd, ?_⟩,
      Subgroup.le_normalizer hyK, hL.pLayerOf_ne_bot, hL.isPCompIn, ?_⟩⟩
  · rw [inf_eq_left.2 hDcomm]
    exact hDrank
  · rw [hLself]; exact hL.isPCompIn_self

end CFSG.GH74.Generic.BProg.B3
