module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase234
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenIleY

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open scoped MatrixGroups
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem isSylowOf_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} [Fact p.Prime] (e : X ≃* Y) {P : Subgroup X}
    (h : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map e.toMonoidHom) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, hP, hdvd⟩ := h
  refine ⟨le_top, hP.map e.toMonoidHom, ?_⟩
  rw [Subgroup.relIndex_top_right,
    Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  simpa only [Subgroup.relIndex_top_right] using hdvd

theorem normalizer_sup_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (P E : Subgroup X)
    (h : Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) ⊔
      Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup Y) : Set Y) = ⊤) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  have hnormP : Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (P : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq P e).symm
  have hnormE : Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (E : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq E e).symm
  rw [hnormP, hnormE] at h
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  have hcomp : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id X := by
    ext x
    simp
  simpa only [Subgroup.map_map, hcomp, Subgroup.map_id] using hmap

theorem dvd_card_of_isSLType {X : Type} [Group X] [Finite X] {p d : ℕ}
    (hp : p.Prime) (hX : IsSLType 2 (ZMod p) X)
    (hd : d.Prime) (hd2 : d ≠ 2)
    (hdvd : d ∣ Nat.card (MulAut X)) : d ∣ Nat.card X := by
  by_contra hnd
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨δ, hδ⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have hδ1 : δ = 1 := mulAut_eq_one_of_not_dvd_card hp hd hd2 hnd hX δ hδ
  have hd1 : d = 1 := by
    rw [← hδ, hδ1]
    simp
  exact hd.ne_one hd1

theorem eq_top_of_index_eq_two_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G]
    (H : Subgroup G) (hidx : H.index = 2) : H = ⊤ := by
  letI : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hquot : Nat.card (G ⧸ H) = 2 := H.index_eq_card.symm.trans hidx
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hquot
  have hle : commutator G ≤ H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  exact top_le_iff.mp (by rw [← Group.IsPerfect.commutator_eq_top]; exact hle)

theorem normalizer_sup_sl2_five (P E : Subgroup (SL(2, ZMod 5))) (d : ℕ)
    (hd : d.Prime) (hd2 : d ≠ 2) (hd3 : d ≠ 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf d E ⊤) :
    Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
      Subgroup.normalizer (E : Set (SL(2, ZMod 5))) = ⊤ := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hXcard : Nat.card (SL(2, ZMod 5)) = 120 := by
    rw [CFSG.PSL2Table.card_SL (F := ZMod 5), ZMod.card]
    norm_num
  haveI : Group.IsPerfect (SL(2, ZMod 5)) := by
    have h4 : ∃ s : Finset (ZMod 5), s.card = 4 := by
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod 5)))
        (n := 4) (by rw [Finset.card_univ, ZMod.card]; norm_num)
      exact ⟨s, hs⟩
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect (K := ZMod 5) h4
  by_cases hd5 : d = 5
  · subst d
    let U : Subgroup (SL(2, ZMod 5)) := CFSG.PSL2Table.unipSL (ZMod 5)
    have hUcard : Nat.card U = 5 := by
      dsimp [U]
      rw [CFSG.PSL2Table.card_unipSL (F := ZMod 5), ZMod.card]
    have hU : CFSG.ABGLocalTools.IsSylowOf 5 U ⊤ := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card (P := U) (K := ⊤) le_top ?_
      rw [hUcard, Subgroup.card_top, factorization_card_SL2_zmod 5]
      norm_num
    obtain ⟨k, -, hk⟩ := hU.exists_mem_conj hE
    have hEeq : E = (U.map (MulAut.conj k).toMonoidHom : Subgroup (SL(2, ZMod 5))) := by
      ext x
      rw [hk x]
      constructor
      · intro hx
        exact ⟨k⁻¹ * x * k, hx, by
          change k * (k⁻¹ * x * k) * k⁻¹ = x
          group⟩
      · rintro ⟨u, hu, rfl⟩
        change k⁻¹ * (k * u * k⁻¹) * k ∈ U
        have h : k⁻¹ * (k * u * k⁻¹) * k = u := by group
        rwa [h]
    have hnormE : Subgroup.normalizer (E : Set (SL(2, ZMod 5))) =
        (Subgroup.normalizer (U : Set (SL(2, ZMod 5)))).map
          (MulAut.conj k).toMonoidHom := by
      rw [hEeq, Subgroup.map_equiv_normalizer_eq]
    have hNcard : Nat.card (Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) = 20 := by
      rw [hnormE, Subgroup.card_map_of_injective (MulAut.conj k).injective]
      change Nat.card (Subgroup.normalizer
        (CFSG.PSL2Table.unipSL (ZMod 5) : Set (SL(2, ZMod 5)))) = 20
      rw [normalizer_unipSL_eq_borelSL, CFSG.PSL2Table.card_borelSL (F := ZMod 5), ZMod.card]
    have hPcard : Nat.card P = 3 := by
      have h := hP.card_eq
      rw [Subgroup.card_top] at h
      have hfac : (Nat.card (SL(2, ZMod 5))).factorization 3 = 1 := by
        rw [hXcard]
        rw [show (120 : ℕ) = 3 * 40 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 40),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]
      rw [hfac] at h
      simpa using h
    have hzord : orderOf (-1 : SL(2, ZMod 5)) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]
      · refine CFSG.PSL2Table.neg_one_ne_one_SL (F := ZMod 5) ?_
        intro h
        have := (ZMod.natCast_eq_zero_iff 2 5).mp h
        norm_num at this
    have hz_normalizes : Subgroup.zpowers (-1 : SL(2, ZMod 5)) ≤
        Subgroup.normalizer (P : Set (SL(2, ZMod 5))) :=
      (Subgroup.zpowers_le.mpr CFSG.PSL2Table.neg_one_mem_center).trans
        (Subgroup.center_le_normalizer (P : Set (SL(2, ZMod 5))))
    have hdisj : Disjoint P (Subgroup.zpowers (-1 : SL(2, ZMod 5))) := by
      rw [disjoint_iff]
      apply Subgroup.eq_bot_of_card_eq
      have hdvd3 : Nat.card ↥(P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5))) ∣ 3 := by
        rw [← hPcard]
        exact Subgroup.card_dvd_of_le
          (H := P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5))) (K := P)
          (show P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5)) ≤ P from inf_le_left)
      have hdvd2 : Nat.card ↥(P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5))) ∣ 2 := by
        have h := Subgroup.card_dvd_of_le (H := P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5)))
          (K := Subgroup.zpowers (-1 : SL(2, ZMod 5)))
          (show P ⊓ Subgroup.zpowers (-1 : SL(2, ZMod 5)) ≤
            Subgroup.zpowers (-1 : SL(2, ZMod 5)) from inf_le_right)
        rwa [Nat.card_zpowers, hzord] at h
      exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 2) hdvd3 hdvd2
    have hsupcard : Nat.card ↥(P ⊔ Subgroup.zpowers (-1 : SL(2, ZMod 5))) =
        Nat.card P * Nat.card (Subgroup.zpowers (-1 : SL(2, ZMod 5))) :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P
        (Subgroup.zpowers (-1 : SL(2, ZMod 5))) hz_normalizes hdisj
    have h6 : Nat.card ↥(P ⊔ Subgroup.zpowers (-1 : SL(2, ZMod 5))) = 6 := by
      rw [hsupcard, hPcard, Nat.card_zpowers, hzord]
    have h6dvd : 6 ∣ Nat.card (Subgroup.normalizer (P : Set (SL(2, ZMod 5)))) := by
      have hsup_le : P ⊔ Subgroup.zpowers (-1 : SL(2, ZMod 5)) ≤
          Subgroup.normalizer (P : Set (SL(2, ZMod 5))) :=
        sup_le Subgroup.le_normalizer hz_normalizes
      have h := Subgroup.card_dvd_of_le
        (H := P ⊔ Subgroup.zpowers (-1 : SL(2, ZMod 5)))
        (K := Subgroup.normalizer (P : Set (SL(2, ZMod 5)))) hsup_le
      rwa [h6] at h
    have h60 : 60 ∣ Nat.card ↥(Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
        Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) := by
      have h6' : 6 ∣ Nat.card ↥(Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
          Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) :=
        h6dvd.trans (Subgroup.card_dvd_of_le
          (H := Subgroup.normalizer (P : Set (SL(2, ZMod 5))))
          (K := Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
            Subgroup.normalizer (E : Set (SL(2, ZMod 5))))
          (show Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ≤ _ from le_sup_left))
      have h20' : 20 ∣ Nat.card ↥(Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
          Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) := by
        rw [← hNcard]
        exact Subgroup.card_dvd_of_le
          (H := Subgroup.normalizer (E : Set (SL(2, ZMod 5))))
          (K := Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
            Subgroup.normalizer (E : Set (SL(2, ZMod 5))))
          (show Subgroup.normalizer (E : Set (SL(2, ZMod 5))) ≤ _ from le_sup_right)
      have h := Nat.lcm_dvd h6' h20'
      rwa [show Nat.lcm 6 20 = 60 by norm_num] at h
    by_contra hne
    have hcard_le : Nat.card ↥(Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
        Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) ≤ 120 := by
      rw [← hXcard]
      simpa only [Subgroup.card_top] using Subgroup.card_le_of_le
        (H := Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
          Subgroup.normalizer (E : Set (SL(2, ZMod 5)))) (K := ⊤) le_top
    obtain ⟨l, hl⟩ := h60
    have hlpos : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · rw [h0, mul_zero] at hl
        exact (Nat.card_pos.ne' hl).elim
      · exact hpos
    have hl2 : l ≤ 2 := by
      have hle : 60 * l ≤ 120 := by
        rw [← hl]
        exact hcard_le
      omega
    have hl12 : l = 1 ∨ l = 2 := by omega
    rcases hl12 with rfl | rfl
    · have hidx : (Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
          Subgroup.normalizer (E : Set (SL(2, ZMod 5)))).index = 2 := by
        rw [Subgroup.index_eq_card_div, hl, hXcard]
      exact hne (eq_top_of_index_eq_two_of_isPerfect _ hidx)
    · have htop : Subgroup.normalizer (P : Set (SL(2, ZMod 5))) ⊔
          Subgroup.normalizer (E : Set (SL(2, ZMod 5))) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hl, hXcard])
      exact hne htop
  ·
    have hdvdX : ¬ d ∣ Nat.card (SL(2, ZMod 5)) := by
      rw [hXcard]
      intro h120
      have h' : d ∣ 2 ^ 3 * (3 * 5) := by
        rw [show 2 ^ 3 * (3 * 5) = 120 by norm_num]
        exact h120
      rcases hd.dvd_mul.mp h' with h2 | h35
      · have h2' : d ∣ 2 := hd.dvd_of_dvd_pow h2
        exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2')
      · rcases hd.dvd_mul.mp h35 with h3 | h5
        · exact hd3 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h3)
        · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5)
    have hEbot : E = ⊥ := by
      have hcardE := hE.card_eq
      rw [Subgroup.card_top] at hcardE
      have hfac : (Nat.card (SL(2, ZMod 5))).factorization d = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hdvdX
      rw [hfac, pow_zero] at hcardE
      exact Subgroup.eq_bot_of_card_eq E hcardE
    rw [hEbot]
    have hbotnorm : Subgroup.normalizer
        ((⊥ : Subgroup (SL(2, ZMod 5))) : Set (SL(2, ZMod 5))) = ⊤ :=
      Subgroup.normalizer_eq_top (⊥ : Subgroup (SL(2, ZMod 5)))
    rw [hbotnorm]
    simp

theorem normalizer_sup_of_isSLType_five {X : Type} [Group X] [Finite X]
    (hX : IsSLType 2 (ZMod 5) X) (P E : Subgroup X) (d : ℕ)
    (hd : d.Prime) (hd2 : d ≠ 2) (hd3 : d ≠ 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hE : CFSG.ABGLocalTools.IsSylowOf d E ⊤) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hX
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 (P.map e.toMonoidHom) ⊤ :=
    isSylowOf_map_mulEquiv e hP
  have hE' : CFSG.ABGLocalTools.IsSylowOf d (E.map e.toMonoidHom) ⊤ :=
    isSylowOf_map_mulEquiv e hE
  exact normalizer_sup_of_mulEquiv e P E
    (normalizer_sup_sl2_five (P.map e.toMonoidHom) (E.map e.toMonoidHom) d hd hd2 hd3 hP' hE')

@[expose] def ThreeTenCase4ExtFiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 3 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X →
    d.Prime → d ≠ 2 → d ≠ 3 →
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

theorem threeTenCase4FiniteInput_of_ext (hExt : ThreeTenCase4ExtFiniteInput) :
    ThreeTenCase4FiniteInput := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX d hd hd2 hd3 hdvd
    rw [ThreeTenCase4SmallType] at hX
    rcases hX with hSL | hExtX
    · exact dvd_card_of_isSLType Nat.prime_five hSL hd hd2 hdvd
    · exact hExt.1 X hExtX d hd hd2 hd3 hdvd
  · intro X _ _ P E d hX hd hd2 hd3 hP hE
    rw [ThreeTenCase4SmallType] at hX
    rcases hX with hSL | hExtX
    · exact normalizer_sup_of_isSLType_five hSL P E d hd hd2 hd3 hP hE
    · exact hExt.2 X P E d hExtX hd hd2 hd3 hP hE

end CFSG.LocalAnalysis.AGL81I.Section3
