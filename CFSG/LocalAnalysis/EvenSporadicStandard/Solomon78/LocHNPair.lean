module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarMain
public import CFSG.Sporadic.HN

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

@[expose] def HNShape {X : Type} [Group X] (t : X) : Prop :=
  ∃ E : Subgroup ↥(centralizer ({t} : Set X)),
    IsHSCover ↥(centralizer ({t} : Set X)) E ∧ E.index = 2

theorem HNShape.map {X X' : Type} [Group X] [Group X'] (f : X ≃* X') {t : X} (h : HNShape t) :
    HNShape (f t) := by
  obtain ⟨E, hE, hi⟩ := h
  let g := centralizerMulEquiv f (z := t) (w := f t) rfl
  exact ⟨E.map (g : ↥(centralizer ({t} : Set X)) →* ↥(centralizer ({f t} : Set X'))), hE.map g,
    by rw [Subgroup.index_map_equiv]; exact hi⟩

theorem card_centralizer_eq_of_isConj {X : Type} [Group X] {a b : X} (h : IsConj a b) :
    Nat.card ↥(centralizer ({a} : Set X)) = Nat.card ↥(centralizer ({b} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact Nat.card_congr (centralizerMulEquiv (MulAut.conj c) (z := a) (w := b)
    (by rw [MulAut.conj_apply]; exact hc)).toEquiv

theorem HNShape.of_isConj {X : Type} [Group X] {a b : X} (h : IsConj a b) (ha : HNShape a) :
    HNShape b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have := ha.map (MulAut.conj c)
  rwa [MulAut.conj_apply, hc] at this

open CFSG.RankThree.PartOne.HNRed in
theorem hnShape_aJ :
    HNShape aJ := by
  have hs := sign_core_aux t6C coe_t6C (MonoidHom.mem_ker.1 t6C_mem_ker) t6C_central
  have hd := coverData_aux t6C t6C_mem_ker t6C_ne_one t6C_central
  exact ⟨Dsub.comap phi6, hd.isHSCover hs.2, hd.index_comap⟩

theorem hnShape_of_card
    {t : ↥JH} (ht : orderOf t = 2) (hc : 88704000 ≤ Nat.card ↥(centralizer ({t} : Set ↥JH))) :
    HNShape t := by
  rcases isConj_aJ_or_t4J ht with h | h
  · exact HNShape.of_isConj h hnShape_aJ
  · have := card_centralizer_eq_of_isConj h
    rw [card_CJ_t4] at this
    omega

theorem exists_mulEquiv_JH_of_isSporadic {Y : Type} [Group Y]
    (h : IsSporadic Y .HN) :
    Nonempty (Y ≃* ↥JH) := by
  obtain ⟨e⟩ := h
  have e' : Y ≃* CFSG.Blueprint.NativeSporadic.HN := e
  exact ⟨e'.trans hnEquivJ⟩

theorem hn_pair_cover_of_shape
    {G J : Type} [Group G] [Finite G] [Group J] {L K : Subgroup G} {u : G}
    (hshape : ∀ t : J, orderOf t = 2 → 88704000 ≤ Nat.card ↥(centralizer ({t} : Set J)) →
      HNShape t)
    (Ψ : ↥L ≃* J) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : Nat.card K = 88704000) :
    IsHSCover ↥(L ⊓ centralizer ({u} : Set G)) (K.subgroupOf (L ⊓ centralizer ({u} : Set G))) ∧
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).index = 2 := by
  set Cu : Subgroup G := L ⊓ centralizer ({u} : Set G) with hCu
  have hKC : K ≤ Cu := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  let u' : ↥L := ⟨u, hu⟩
  have ht₀ : orderOf (Ψ u') = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu2
  let ψ : ↥Cu ≃* ↥(centralizer ({Ψ u'} : Set J)) :=
    (infCentralizerMulEquiv hu).trans (centralizerMulEquiv Ψ (z := u') (w := Ψ u') rfl)
  have hKcard : Nat.card ↥(K.subgroupOf Cu) = 88704000 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hcard]
  have hge : 88704000 ≤ Nat.card ↥(centralizer ({Ψ u'} : Set J)) := by
    rw [← Nat.card_congr ψ.toEquiv, ← hKcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨E₀, hE₀, hi₀⟩ := hshape _ ht₀ hge
  have hE₁ : IsHSCover ↥Cu (E₀.map (ψ.symm : ↥(centralizer ({Ψ u'} : Set J)) →* ↥Cu)) :=
    hE₀.map ψ.symm
  have hi₁ : (E₀.map (ψ.symm : ↥(centralizer ({Ψ u'} : Set J)) →* ↥Cu)).index = 2 := by
    rw [Subgroup.index_map_equiv]
    exact hi₀
  have hCuCard : Nat.card ↥Cu = 177408000 := by
    have h1 := card_eq_of_double_cover hE₀.card_center hE₀.quotient
    have h2 := Subgroup.card_mul_index E₀
    rw [h1, hi₀] at h2
    rw [Nat.card_congr ψ.toEquiv]
    omega
  have hKi : (K.subgroupOf Cu).index = 2 := by
    have h2 := Subgroup.card_mul_index (K.subgroupOf Cu)
    rw [hKcard, hCuCard] at h2
    omega
  have heq : K.subgroupOf Cu = E₀.map (ψ.symm : ↥(centralizer ({Ψ u'} : Set J)) →* ↥Cu) :=
    eq_of_index_two_of_isPerfect hE₁.perfect hi₁ hKi
  exact ⟨heq ▸ hE₁, hKi⟩

theorem hn_pair_cover
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .HN) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : Nat.card K = 88704000) :
    IsHSCover ↥(L ⊓ centralizer ({u} : Set G)) (K.subgroupOf (L ⊓ centralizer ({u} : Set G))) ∧
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).index = 2 := by
  obtain ⟨Ψ⟩ := exists_mulEquiv_JH_of_isSporadic hL
  exact hn_pair_cover_of_shape (fun _ ht hc => hnShape_of_card ht hc) Ψ hu hu2 hKL hKu hcard

theorem hn_card_eq {G : Type} [Group G] {L : Subgroup G}
    (hL : IsSporadic L .HN) :
    Nat.card ↥L = 273030912000000 := by
  obtain ⟨e⟩ := hL
  have e' : ↥L ≃* CFSG.Blueprint.NativeSporadic.HN := e
  rw [Nat.card_congr e'.toEquiv]
  exact CFSG.Sporadic.HN.card_HN

theorem hn_factorization_two : (273030912000000 : ℕ).factorization 2 = 14 := by
  have h : (273030912000000 : ℕ) = 2 ^ 14 * 16664484375 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.EvenSporadicStandard.Solomon78
