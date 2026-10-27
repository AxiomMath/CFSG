module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2Inner

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] {B T X : Subgroup H}

theorem map_subtype_normalizerMonoidHom {B : Subgroup H} {t : H}
    (ht : t ∈ normalizer (B : Set H)) (K : Subgroup B) :
    (K.map (B.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom).map B.subtype =
      conjSubgroup t (K.map B.subtype) := by
  rw [conjSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_normalizer_of_conjSubgroup_eq {t : H} {K : Subgroup H}
    (hK : conjSubgroup t K = K) : t ∈ normalizer (K : Set H) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : t * x * t⁻¹ ∈ conjSubgroup t K := conj_mem_conjSubgroup hx
    rwa [hK] at this
  · intro hx
    have h1 : t * x * t⁻¹ ∈ conjSubgroup t K := hK.symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    rw [← this]
    exact hy

theorem Hyp46.false_of_highestRootData [Finite H] (h : Hyp46 B T X)
    (hB : Open.IsQuasisimple B) (D : HighestRootData B) : False := by
  classical
  set F := GaloisField D.p D.e
  have hF : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F D.p
    rw [Nat.card_eq_fintype_card, hn]
    exact (hp.odd_of_ne_two D.odd).pow
  let φ : T →* MulAut B := B.normalizerMonoidHom.comp (Subgroup.inclusion h.le_normalizer)
  have hφ : ∀ t (ht : t ∈ T), φ ⟨t, ht⟩ = B.normalizerMonoidHom ⟨t, h.le_normalizer ht⟩ :=
    fun _ _ => rfl
  have h𝒯 : IsPGroup 2 φ.range :=
    h.sylow.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := D.commuting φ.range h𝒯
  set J₀ : Subgroup B := conjSubgroup g D.J with hJ₀
  set J' : Subgroup H := J₀.map B.subtype with hJ'
  have hJ'B : J' ≤ B := Subgroup.map_subtype_le _
  have e' : J' ≃* SL(2, F) :=
    ((J₀.equivMapOfInjective B.subtype B.subtype_injective).symm.trans
      (D.J.equivMapOfInjective _ (MulAut.conj g).injective).symm).trans D.equivJ.some
  have hcomm : ∀ t ∈ T, conjSubgroup t J' = J' ∨
      ∀ a ∈ J', ∀ b ∈ conjSubgroup t J', a * b = b * a := by
    intro t ht
    have hconj : conjSubgroup t J' = (J₀.map (φ ⟨t, ht⟩).toMonoidHom).map B.subtype := by
      rw [hφ, map_subtype_normalizerMonoidHom]
    rcases hg (φ ⟨t, ht⟩) ⟨⟨t, ht⟩, rfl⟩ with h1 | h1
    · left
      rw [hconj, h1]
    · right
      rw [hconj]
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
      exact congrArg Subtype.val (h1 a' ha' b' hb')
  have hTJ'C : T ≤ centralizer (J' : Set H) := by
    by_cases hmove : ∃ u ∈ T, conjSubgroup u J' ≠ J'
    · obtain ⟨u, hu, hne⟩ := hmove
      exact (h.false_of_moved e' hF hJ'B hcomm hu hne).elim
    · push Not at hmove
      have hTJ' : T ≤ normalizer (J' : Set H) := fun t ht =>
        mem_normalizer_of_conjSubgroup_eq (hmove t ht)
      by_cases hC : T ⊓ centralizer (J' : Set H) = ⊥
      · exact ((h.restrict hJ'B hTJ' hC).false_of_sl2 e' hF).elim
      · exact h.le_centralizer_of_inf_ne_bot e' hF hJ'B hTJ' hC
  set P₀ : Subgroup B := pCoreOf D.p (normalizer (D.V : Set B))
  set Q₀ : Subgroup B := conjSubgroup g P₀ with hQ₀
  set V' : Subgroup B := conjSubgroup g D.V with hV'
  have hQ₀eq : Q₀ = pCoreOf D.p (normalizer (V' : Set B)) := by
    rw [hQ₀, hV', conjSubgroup, conjSubgroup, ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv,
      Subgroup.map_equiv_normalizer_eq]
  have hgen : Q₀ ⊔ J₀ = ⊤ := by
    rw [hQ₀, hJ₀, conjSubgroup, conjSubgroup, ← Subgroup.map_sup, D.gen,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  have hV'J₀ : V' ≤ J₀ := Subgroup.map_mono D.V_le
  set Q : Subgroup H := Q₀.map B.subtype with hQ
  have hTQ : T ≤ normalizer (Q : Set H) := by
    intro t ht
    set ψ := B.normalizerMonoidHom ⟨t, h.le_normalizer ht⟩ with hψ
    have hψV : V'.map ψ.toMonoidHom = V' := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hwJ : (w : H) ∈ J' := Subgroup.mem_map_of_mem _ (hV'J₀ hw)
        have : ψ w = w := by
          apply Subtype.ext
          rw [hψ, Subgroup.normalizerMonoidHom_apply_apply_coe]
          show t * (w : H) * t⁻¹ = w
          rw [← (mem_centralizer_iff.mp (hTJ'C ht)) w hwJ]
          group
        simpa [this] using hw
      · intro hv
        refine ⟨v, hv, ?_⟩
        have hvJ : (v : H) ∈ J' := Subgroup.mem_map_of_mem _ (hV'J₀ hv)
        apply Subtype.ext
        rw [MulEquiv.coe_toMonoidHom, hψ, Subgroup.normalizerMonoidHom_apply_apply_coe]
        show t * (v : H) * t⁻¹ = v
        rw [← (mem_centralizer_iff.mp (hTJ'C ht)) v hvJ]
        group
    have hψQ : Q₀.map ψ.toMonoidHom = Q₀ := by
      rw [hQ₀eq, ← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv, Subgroup.map_equiv_normalizer_eq,
        hψV]
    refine mem_normalizer_of_conjSubgroup_eq ?_
    rw [hQ, ← map_subtype_normalizerMonoidHom (h.le_normalizer ht), ← hψ, hψQ]
  have hQodd : Odd (Nat.card Q) := by
    have : Fact D.p.Prime := D.fact
    have hpg : IsPGroup D.p Q₀ := by
      rw [hQ₀eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup D.p _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    rw [hQ, Subgroup.card_map_of_injective B.subtype_injective, hk]
    exact (D.fact.out.odd_of_ne_two D.odd).pow
  have hQX : Q ≤ normalizer (X : Set H) :=
    h.le_normalizer_of_odd ((Subgroup.map_subtype_le _).trans le_sup_right) hTQ hQodd
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ : ∃ t : T, t ≠ 1 := by
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by linarith [h.four_le])
    exact _root_.exists_ne 1
  have ht₀1' : t₀ ≠ 1 := fun h1 => ht₀1 (Subtype.ext h1)
  have hJ'X : J' ≤ normalizer (X : Set H) := fun x hx =>
    h.inf_centralizer_le_of_mem ht₀ ht₀1' (Subgroup.mem_inf.mpr ⟨mem_sup_right (hJ'B hx), by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hTJ'C ht₀)) x hx⟩)
  have hBX : B ≤ normalizer (X : Set H) := by
    have hB' : B = Q ⊔ J' := by
      rw [hQ, hJ', ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hB']
    exact sup_le hQX hJ'X
  have heven : Even (Nat.card B) := by
    have hz : orderOf (centralInv e') = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, sl2_orderOf_neg_one hF]
    have h2 := Subgroup.orderOf_dvd_natCard B (hJ'B (centralInv_mem e'))
    rw [hz] at h2
    exact even_iff_two_dvd.mpr h2
  exact h.false_of_le_normalizer hB heven hBX

end CFSG.ComponentClassification.RankTwoOddLie
