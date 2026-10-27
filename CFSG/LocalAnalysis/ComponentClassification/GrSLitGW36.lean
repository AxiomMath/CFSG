module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW35
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem not_dvd_card_of_perfect_of_sylow_le_center {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (hP : (P : Subgroup K) ≤ center K) : ¬ p ∣ Nat.card K := by
  have hnc : normalizer ((P : Subgroup K) : Set K) ≤ centralizer ((P : Subgroup K) : Set K) :=
    fun g _ => mem_centralizer_iff.mpr fun h hh => (mem_center_iff.mp (hP hh) g).symm
  have hker : (MonoidHom.transferSylow P hnc).ker = ⊤ := by
    refine top_unique ?_
    rw [← (Group.IsPerfect.commutator_eq_top : commutator K = ⊤)]
    refine commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (mem_center_iff.mp (hP (MonoidHom.transferSylow P hnc b).2) _)
  have h := MonoidHom.not_dvd_card_ker_transferSylow P hnc
  rwa [hker, card_top] at h

variable {X : Type} [Group X] [Finite X]

theorem even_card_of_isComponent (hX : pPrimeCore 2 X = ⊥) {J : Subgroup X}
    (hJ : IsComponent J) : Even (Nat.card J) := by
  by_contra h
  have hbot := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hX hJ.2 (Nat.not_even_iff_odd.mp h)
  have : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial
    ((CFSG.isComponent_iff_open J).mp hJ).2.2
  exact (J.nontrivial_iff_ne_bot.mp this) hbot

theorem mem_normalizer_component_of_centralizer (hX : pPrimeCore 2 X = ⊥) {Y : Subgroup X}
    (hY : Y = generalizedFitting X) (S : Sylow 2 Y) {x : X}
    (hx : x ∈ centralizer (((S : Subgroup Y).map Y.subtype : Subgroup X) : Set X))
    {J : Subgroup X} (hJ : IsComponent J) : x ∈ normalizer (J : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup X := (S : Subgroup Y).map Y.subtype with hS'
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map Y.subtype
  have hS'Y : S' ≤ Y := map_subtype_le _
  obtain ⟨S₀, hS₀⟩ := hS'2.exists_le_sylow
  have hS₀Y : (S₀ : Subgroup X) ⊓ Y ≤ S' := by
    have hQ : IsPGroup 2 (((S₀ : Subgroup X) ⊓ Y).subgroupOf Y) :=
      (S₀.isPGroup'.to_le inf_le_left).comap_of_injective Y.subtype Y.subtype_injective
    have hSQ : (S : Subgroup Y) ≤ ((S₀ : Subgroup X) ⊓ Y).subgroupOf Y := by
      intro s hs
      rw [mem_subgroupOf]
      exact ⟨hS₀ ⟨s, hs, rfl⟩, s.2⟩
    have heq := S.is_maximal' hQ hSQ
    intro y hy
    have hy' : (⟨y, (mem_inf.mp hy).2⟩ : Y) ∈ ((S₀ : Subgroup X) ⊓ Y).subgroupOf Y := hy
    rw [heq] at hy'
    exact ⟨_, hy', rfl⟩
  have hJY : J ≤ Y := by
    rw [hY]
    exact (le_sSup hJ : J ≤ layer X).trans le_sup_right
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S₀ hJ.2
  have hPS' : ∀ t : J, t ∈ (P : Subgroup J) → (t : X) ∈ S' := by
    intro t ht
    have h1 : (t : X) ∈ (S₀ : Subgroup X) ⊓ J := hP ▸ mem_map_of_mem J.subtype ht
    exact hS₀Y (mem_inf.mpr ⟨(mem_inf.mp h1).1, hJY (mem_inf.mp h1).2⟩)
  have hJ' := (CFSG.isComponent_iff_open J).mp hJ
  by_cases heq : J.map (MulAut.conj x).toMonoidHom = J
  · exact mem_normalizer_iff_map_conj_eq.mpr heq
  exfalso
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne J _ hJ'
    ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj x) J).mpr hJ')
    (Ne.symm heq)
  have hle := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hPc : (P : Subgroup J) ≤ center J := by
    intro t ht
    have htx : (t : X) ∈ J.map (MulAut.conj x).toMonoidHom := by
      refine ⟨t, t.2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← mem_centralizer_iff.mp hx _ (hPS' t ht), mul_inv_cancel_right]
    exact mem_center_iff.mpr fun j =>
      Subtype.ext (mem_centralizer_iff.mp (hle j.2) _ htx).symm
  have : Group.IsPerfect J := ⟨hJ'.2.2.1⟩
  exact not_dvd_card_of_perfect_of_sylow_le_center P hPc
    (even_iff_two_dvd.mp (even_card_of_isComponent hX hJ))

theorem pLayer_le_normalizer_of_isPComponent {K : Subgroup X} (hK : IsPComponent 2 K) :
    pLayer X 2 ≤ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ, -, hKJ, -⟩ := id hK
  refine sSup_le fun K' hK' k' hk' => ?_
  apply UnbalancedLayer.mem_normalizer_of_map hK
  obtain ⟨J', hJ', -, hK'J', -⟩ := hK'
  have hk'J' : QuotientGroup.mk' (pPrimeCore 2 X) k' ∈ J' := hK'J' ▸ mem_map_of_mem _ hk'
  rw [hKJ]
  by_cases heq : J' = J
  · rw [heq] at hk'J'
    exact le_normalizer hk'J'
  · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne J' J
      ((CFSG.isComponent_iff_open J').mp hJ') ((CFSG.isComponent_iff_open J).mp hJ) heq
    exact ((commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (centralizer_le_normalizer _)) hk'J'

theorem oddCore_centralizer_sylow_le_normalizer (T : Sylow 2 (lTwoPrimeTwo X))
    {K : Subgroup X} (hK : IsPComponent 2 K) :
    (pPrimeCore 2 (centralizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype : Subgroup X) :
      Set X))).map (centralizer (((T : Subgroup _).map (lTwoPrimeTwo X).subtype : Subgroup X) :
        Set X)).subtype ≤ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set T' : Subgroup X := (T : Subgroup (lTwoPrimeTwo X)).map (lTwoPrimeTwo X).subtype with hT'
  set Yb : Subgroup (X ⧸ pPrimeCore 2 X) := (lTwoPrimeTwo X).map π with hYb
  let S : Sylow 2 Yb := T.mapSurjective (MonoidHom.subgroupMap_surjective π (lTwoPrimeTwo X))
  have hS : (S : Subgroup Yb).map Yb.subtype = T'.map π := by
    change ((T : Subgroup (lTwoPrimeTwo X)).map (π.subgroupMap (lTwoPrimeTwo X))).map
      Yb.subtype = _
    rw [map_map, hT', map_map]
    rfl
  obtain ⟨J, hJ, -, hKJ, -⟩ := id hK
  intro f hf
  apply UnbalancedLayer.mem_normalizer_of_map hK
  rw [hKJ]
  have hfC : f ∈ centralizer (T' : Set X) := map_subtype_le _ hf
  have hfb : π f ∈ centralizer (((S : Subgroup Yb).map Yb.subtype : Subgroup _) : Set _) := by
    rw [hS, mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hfC t ht]
  exact mem_normalizer_component_of_centralizer (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    map_lTwoPrimeTwo S hfb hJ

theorem oddCore_centralizer_le_normalizer {B : Subgroup X} (hB : IsPGroup 2 B)
    {K : Subgroup X} (hK : IsPComponent 2 K) :
    (pPrimeCore 2 (centralizer (B : Set X))).map (centralizer (B : Set X)).subtype ≤
      normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 (lTwoPrimeTwo X) := Classical.arbitrary _
  refine (oddCore_centralizer_le_lStar hB T).trans (sup_le (sup_le ?_ ?_) ?_)
  · exact pLayer_le_normalizer_of_isPComponent hK
  · exact UnbalancedLayer.pPrimeCore_le_normalizer hK
  · exact oddCore_centralizer_sylow_le_normalizer T hK

end CFSG.ComponentClassification.GrSLit
